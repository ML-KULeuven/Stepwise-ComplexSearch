import copy
from time import time

import cpmpy as cp
from cpmpy.expressions.core import Operator, Comparison
from cpmpy.expressions.globalfunctions import GlobalFunction
from cpmpy.expressions.globalconstraints import GlobalConstraint
from cpmpy.expressions.utils import is_num
from cpmpy.expressions.variables import _NumVarImpl
from cpmpy.solvers.solver_interface import ExitStatus
from cpmpy.transformations.normalize import toplevel_list
from tqdm import tqdm

from .parsing import PumpkinProofParser
from .simplify import simplify_proof
from .minimize import minimize_proof

from .utils import sanity_check_proof, get_variables, print_proof_statistics, pretty_print_sequence, \
    print_sequence_statistics

def compute_sequence(*args, **kwargs):

    proof = compute_explanation_proof(*args, **kwargs)
    return finalize_sequence(proof)


def compute_explanation_proof(model,
                              minimization_phase1 = "proof",
                              minimization_phase2 = "global",
                              mus_solver = "exact",
                              mus_type="smus",
                              proof_name="proof.drcp",
                              do_sanity_check = False,
                              verbose = 0,
                              orig_proof = None,
                              solver_cons_to_user_cons = None,
                              time_limit=None,
                              seed =0
                              ):
    """
        Compute a step-wise explanation sequence by starting from a DRCP proof.
        The pipeline consists of the following steps
        1. Solve model and parse proof
        2. Remove steps with auxiliary variables
        4. Replace solver-level constraints with user-level constraints
        6. [Optional] Minimize reasons in the proof
        5. Remove steps deriving clauses over multiple variables
        6. [Optional] Minimize reasons in the proof

    :param model: Unsatisfiable CPMpy model
    :param minimization_phase1: Which type of proof minimization we want to do in the first phase
                                Can be any of:
                                    proof: don't do anything
                                    trim: trim the proof based on the reasons in the proof
                                    mus: trim the proof using MUS-minimization
                                    smus: trim the proof using Smallest-MUS minimization
    :param minimization_phase2: Which type of proof minimization we want to do in the second phase
                                Can be any of:
                                    proof: don't do anything
                                    trim: trim the proof based on the reasons in the proof
                                    mus: trim the proof using MUS-minimization
                                    smus: trim the proof using Smallest-MUS minimization
    :param mus_solver: which solver to use during MUS/SMUS minimization
    :param mus_type: which type of MUS to use: deletion-based MUS or SMUS
    :param proof_name: the name of the proof stored on disk
    :param do_sanity_check: For debugging, check whether the proof is valid
    :param verbose: set verbosity and print statistics of proof
    :param pumpkin_solver: CPMpy Pumpkin solver, only needed to run experiments, to ensure proof is re-used among configs
    :return: sequence of explanation steps
    """

    timings = dict()
    if orig_proof is None:

        # cons = toplevel_list(model.constraints, merge_and=False)
        # cons = [c for c in cons if not (isinstance(c, cp.BoolVal) and c.value() is True)]

        solver = PumpkinProofParser(model, proof=proof_name, seed=seed)

        assert solver.solve(time_limit=time_limit) is False
        if solver.status().exitstatus == ExitStatus.UNKNOWN:
            raise TimeoutError("Initial solve call timed out")
        if verbose > 0:
            print(f"Took {solver.status().runtime}seconds to solve model and produce proof")
        timings['solve_time'] = solver.status().runtime
        # read the proof from disk
        solver_cons_to_user_cons = solver.user_cons
        orig_proof = solver.read_proof_tree()
    else:
        assert solver_cons_to_user_cons is not None, "Must provide solver_cons_to_user_cons if cpm_proof is given"

    if do_sanity_check: sanity_check_proof(orig_proof)
    if verbose > 0:
        print_proof_statistics(orig_proof, "initial proof")

    # Remove steps deriving information about auxiliary variables
    user_vars = frozenset(get_variables(model.constraints))
    def only_user_vars(step):
        return frozenset(get_variables(step['derived'])) <= user_vars

    proof = simplify_proof(orig_proof, condition=only_user_vars)
    if do_sanity_check: sanity_check_proof(proof)
    if verbose > 0:
        print_proof_statistics(proof, "proof without auxiliary variables")

    # Replace solver-level constraints with user-level constraints
    for step in tqdm(proof, desc="Replacing solver-level constraints with user-level constraints"):
        user_reasons = []
        for r in step['reasons']:
            if isinstance(r, int): user_reasons.append(r)
            else:
                user_reasons.append(solver_cons_to_user_cons[r])
        step['reasons'] = user_reasons

    if verbose > 0:
        print_proof_statistics(proof, "proof after replacing inferences with constraints")

    # Do the first minimization phase
    proof = minimize_proof(proof, model,
                           minimization_type=minimization_phase1,
                           mus_type=mus_type, mus_solver=mus_solver,
                           verbose=verbose,  time_limit=time_limit)
    if do_sanity_check: sanity_check_proof(proof)
    if verbose > 0:
        print_proof_statistics(proof, "proof after first minimization phase")

    # Remove steps deriving clauses with more than one variable
    def is_domain_reduction(step):
        return len(get_variables(step['derived'])) <= 1

    proof = simplify_proof(proof, condition=is_domain_reduction)
    if do_sanity_check: sanity_check_proof(proof)
    if verbose > 0:
        print_proof_statistics(proof, "proof with only domain reductions")

    # Do the second minimization phase
    proof = minimize_proof(proof, model,
                           minimization_type=minimization_phase2,
                           mus_type=mus_type, mus_solver=mus_solver,
                           verbose=verbose, time_limit=time_limit)
    if do_sanity_check: sanity_check_proof(proof)
    if verbose > 0:
        print_proof_statistics(proof, "proof after second minimization phase")
    
    return proof, orig_proof
    
def sort_proof(proof):

    derived_at = dict() # mapping from literals to step ids

    new_proof = []
    for step in proof:
        reason_ids = [r for r in step['reasons'] if isinstance(r, int)]
        if len(reason_ids) == 0:
            id_of_step = len(new_proof) # just append
        else:
            latest = max(derived_at[r] for r in reason_ids)
            id_of_step = latest + 1

        new_proof.insert(id_of_step, step)

        # now update the derived_at dict...
        for key, val in derived_at.items():
            if val >= id_of_step:
                derived_at[key] = val + 1

        assert len(set(derived_at.values())) == len(derived_at.values()), "Hmm there are duplicates somehow"

        derived_at[step['id']] = id_of_step


        # and save where we derived these literals

    # need to fixup the steps now
    new_id = dict()
    for i, step in enumerate(new_proof, start=1):
        new_id[step['id']] = i
        step['id'] = i
        new_reasons = []
        for r in step['reasons']:
            if isinstance(r, int):
                new_reasons.append(new_id[r])
            else:
                new_reasons.append(r)
        step['reasons'] = new_reasons

    return new_proof


def minimize_scope(step):
    """
        Not all variables occuring in the constraints are actually required.
        We can simply remove the variables from the arguments of the constraint.
        Some bookkeeping is required to ensure the syntax of the constraint is preserved.

        Currently supported constraints:
            - max
            - NoOverlap
            - Cumulative
        Other constraints will simply be left as-is.
    """
    print("Minimizing scope of step", step)
    step = copy.copy(step)
    lit_vars = frozenset(get_variables(step['input_lits'] +  step['output_lits']))
    cons = []
    for c in step['constraints']:

        if isinstance(c, Comparison): # numerical constraints
            lhs, rhs = c.args
            if isinstance(lhs, GlobalFunction) and lhs.name == "max":
                c = copy.copy(c)
                c.args[0] = cp.max([v for v in lhs.args if set(get_variables(v)) & lit_vars or is_num(v)])

            if isinstance(rhs, GlobalFunction) and rhs.name == "max":
                c = copy.copy(c)
                c.args[1] = cp.max([v for v in rhs.args if set(get_variables(v)) & lit_vars or is_num(v)])

        elif isinstance(c, GlobalConstraint):
            if c.name == "no_overlap":
                start, dur, end = c.args
                assert end is None, "NoOverlap with end times not supported, you should be on the `no_end_no_overlap` branch of CPMpy"
                new_start, new_dur = [], []
                for s,d in zip(start, dur):
                    start_in_lits = set(get_variables(s)) & lit_vars
                    dur_in_lits = set(get_variables(d)) & lit_vars
                    both_constants = is_num(s) and is_num(d)
                    if start_in_lits or dur_in_lits or both_constants:
                        new_start.append(s)
                        new_dur.append(d)
                c = cp.NoOverlap(new_start, new_dur)
            elif c.name == "cumulative":
                new_start, new_dur, new_height = [], [], []
                start, dur, end, height, cap = c.args
                assert end is None, "Cumulative with end times not supported, you should be on the `no_end_cumulative` branch of CPMpy"

                for s, d, h in zip(start, dur, height):
                    start_in_lits = set(get_variables(s)) & lit_vars
                    dur_in_lits = set(get_variables(d)) & lit_vars
                    h_in_lits = set(get_variables(h)) & lit_vars
                    all_constants = is_num(s) and is_num(d) and is_num(h)
                    if start_in_lits or dur_in_lits or h_in_lits or all_constants:
                        new_start.append(s)
                        new_dur.append(d)
                        new_height.append(h)

                c = cp.Cumulative(new_start, new_dur, demand=new_height, capacity=cap)

        cons.append(c)

    step['constraints'] = cons
    return step



from cpmpy.expressions.utils import flatlist
from cpmpy.expressions.core import Expression

def finalize_sequence(seq, extra_lits=[],minimize_scopes=False):
    """
    Finalize the sequence by:
        - merging steps with equal reasons
        - merging steps with equal set of constraints, and all known literals
    """

    known_literals = set(seq[0]['output_lits']+flatlist(extra_lits))
    new_seq = [seq[0]]
    i = 1
    output_lits = list(seq[0]['output_lits'])
    while i < len(seq):
        assert set(seq[i]['input_lits']) <= known_literals, f"Step {i} uses literals which are not known!!,\n{known_literals}, {seq[i]}"

        if set(seq[i]['constraints']) != set(new_seq[-1]['constraints']):
            new_seq.append(seq[i])
            output_lits = list(seq[i]['output_lits']) # reset

        else:
            # two sets of constraints are equal to each other
            prev_step = new_seq[-1]
            output_lits += seq[i]['output_lits']
            prev_step['input_lits'] = list((set(prev_step['input_lits']) | set(seq[i]['input_lits']))- set(output_lits))
            prev_step['output_lits'] += seq[i]['output_lits']


        known_literals |= set(seq[i]['output_lits'])
        i += 1

    # syntactic minimization of input and output literals
    for step in new_seq:
        step['input_lits'] = syntactic_minimize_literals(step['input_lits'])
        step['output_lits'] = syntactic_minimize_literals(step['output_lits'])

    return new_seq


def syntactic_minimize_literals(literals):
    # given two literals x <= v and x <= v + k; just keep the strongest one
    # same for >=
    # others: leave as is

    leq_map = dict() # dict from vars to values for which we found a <= literal
    geq_map = dict() # dict from vars to values for which we found a >= literal

    new_literals = []
    for lit in literals:
        if isinstance(lit, cp.BoolVal) and lit.value() is False:
            return [lit]
        if isinstance(lit, Comparison):
            lhs, rhs = lit.args
            assert isinstance(rhs, int)
            assert isinstance(lhs, _NumVarImpl), f"Expected Intvar on lhs of comparison, but got literal {lit}"
            if lit.name == "<=":
                if lhs not in leq_map:
                    leq_map[lhs] = set()
                leq_map[lhs].add(rhs)
            elif lit.name == "<":
                if lhs not in leq_map:
                    leq_map[lhs] = set()
                leq_map[lhs].add(rhs-1)
            elif lit.name == ">=":
                if lhs not in geq_map:
                    geq_map[lhs] = set()
                geq_map[lhs].add(rhs)
            elif lit.name == ">":
                if lhs not in geq_map:
                    geq_map[lhs] = set()
                geq_map[lhs].add(rhs+1)
            elif lit.name in ("==", "!="):
                new_literals.append(lit)
            else:
                raise ValueError("Unexpected comparison: literal", lit)
        else:
            new_literals.append(lit)

    new_literals += [var <= min(vals) for var, vals in leq_map.items()]
    new_literals += [var >= max(vals) for var, vals in geq_map.items()]

    return new_literals



def finalize_sequence_old(proof, minimize_scopes=False):
    """
    Finialize the sequence by
     - merging steps with equal reasons
     - materializing the reasons of each step
    """
    proof_dict = {step['id'] : step for step in proof}
    # reasons_cache = dict()
    explanation = []
    for step in proof:
        reasons = frozenset(flatlist([proof_dict[r]['derived'] if isinstance(r, int) else r for r in step['reasons']]))
        for prev_step in explanation:
            if reasons <= set(prev_step['input_lits'] + prev_step['constraints'] + prev_step['output_lits']):
                prev_step['output_lits'].extend(step['derived'])
                break
        else:
            input_lits = [proof_dict[id]['derived'] for id in step['reasons'] if isinstance(id,int)]
            if "input_reasons" in step:
                for r in step['input_reasons']:
                    if isinstance(r, int):
                        input_lits.append(proof_dict[r]['derived'])
                    else:
                        assert isinstance(r, Expression)
                        input_lits.append(r)

            expl_step = dict(
                id = step['id'],
                input_lits = minimize_literals(flatlist(input_lits)),
                constraints = [cons for cons in step['reasons'] if isinstance(cons, Expression)],
                output_lits = list(step['derived'])
            )
            # reasons_cache[reasons] = step['id']
            explanation.append(expl_step)

    if minimize_scopes:
        return [minimize_scope(step) for step in explanation]
    return explanation


if __name__ == "__main__":
    import cpmpy as cp

    x, y, z = cp.intvar(0,10, shape=3, name=tuple("xyz"))
    m = cp.intvar(0,10, name="m")

    print(minimize_scope(dict(input_lits=[m <= 5],
                              constraints = [m == cp.max(x,y,z)],
                              output_lits = [x <= 5, y <=5])))
