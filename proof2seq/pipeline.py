import cpmpy as cp
from cpmpy.expressions.core import Comparison
from cpmpy.expressions.utils import flatlist
from cpmpy.expressions.variables import _NumVarImpl
from cpmpy.solvers.solver_interface import ExitStatus

from .parsing import PumpkinProofParser
from .minimize import minimize_proof

from .utils import sanity_check_nogoods, get_variables, print_proof_statistics


def keep_user_var_nogoods(user_vars):
    """Return a keep_step predicate that retains nogoods over user variables only."""
    user_vars = frozenset(user_vars)
    return lambda expr: frozenset(get_variables(expr)) <= user_vars


def is_domain_reduction(expr):
    return len(get_variables(expr)) <= 1


def compute_explanation_proof(
    model,
    minimize_phase1=False,
    minimize_phase2=True,
    mus_solver="exact",
    mus_type="smus",
    proof_name="proof.drcp",
    do_sanity_check=False,
    verbose=0,
    time_limit=None,
    seed=0,
):
    """
        Compute a step-wise explanation proof by starting from a DRCP proof.
        The pipeline consists of the following steps
        1. Solve model and parse proof (filtered to user-variable nogoods)
        2. [Optional] Globally minimize the pool of nogoods
        3. Filter to domain-reduction nogoods
        4. [Optional] Globally minimize again

    :param model: Unsatisfiable CPMpy model
    :param minimize_phase1: whether to minimize before the domain-reduction filter
    :param minimize_phase2: whether to minimize after the domain-reduction filter
    :param mus_solver: which solver to use during MUS/SMUS minimization
    :param mus_type: 'mus' or 'smus'
    :param proof_name: the name of the proof stored on disk
    :param do_sanity_check: For debugging, check whether the nogoods are valid
    :param verbose: set verbosity and print statistics of proof
    :return: (nogoods, orig_nogoods) — both lists of Expressions
    """
    solver = PumpkinProofParser(model, proof=proof_name, seed=seed)

    assert solver.solve(time_limit=time_limit) is False
    if solver.status().exitstatus == ExitStatus.UNKNOWN:
        raise TimeoutError("Initial solve call timed out")
    if verbose > 0:
        print(f"Took {solver.status().runtime}seconds to solve model and produce proof")

    user_vars = frozenset(get_variables(model.constraints))
    orig_proof = solver.read_proof(keep_step=keep_user_var_nogoods(user_vars))

    if do_sanity_check:
        sanity_check_nogoods(orig_proof, model.constraints)
    if verbose > 0:
        print_proof_statistics(orig_proof, "initial proof (user-var nogoods)")

    proof = list(orig_proof)

    if minimize_phase1:
        proof = minimize_proof(proof, model.constraints,
                               mus_type=mus_type, mus_solver=mus_solver,
                               time_limit=time_limit)
        if do_sanity_check:
            sanity_check_nogoods(proof, model.constraints)
        if verbose > 0:
            print_proof_statistics(proof, "proof after first minimization phase")

    # Keep only domain reductions (clauses over at most one variable)
    proof = [ng for ng in proof if is_domain_reduction(ng)]
    if do_sanity_check:
        sanity_check_nogoods(proof, model.constraints)
    if verbose > 0:
        print_proof_statistics(proof, "proof with only domain reductions")

    if minimize_phase2:
        proof = minimize_proof(proof, model.constraints,
                               mus_type=mus_type, mus_solver=mus_solver,
                               time_limit=time_limit)
        if do_sanity_check:
            sanity_check_nogoods(proof, model.constraints)
        if verbose > 0:
            print_proof_statistics(proof, "proof after second minimization phase")

    return proof, orig_proof


def finalize_sequence(seq, extra_lits=[]):
    """
    Finalize the sequence by:
        - merging steps with equal set of constraints
        - syntactically minimizing input/output literals
    """
    known_literals = set(seq[0]['output_lits'] + flatlist(extra_lits))
    new_seq = [seq[0]]
    i = 1
    output_lits = list(seq[0]['output_lits'])
    while i < len(seq):
        assert set(seq[i]['input_lits']) <= known_literals, f"Step {i} uses literals which are not known!!,\n{known_literals}, {seq[i]}"

        if set(seq[i]['constraints']) != set(new_seq[-1]['constraints']):
            new_seq.append(seq[i])
            output_lits = list(seq[i]['output_lits'])
        else:
            prev_step = new_seq[-1]
            output_lits += seq[i]['output_lits']
            prev_step['input_lits'] = list((set(prev_step['input_lits']) | set(seq[i]['input_lits'])) - set(output_lits))
            prev_step['output_lits'] += seq[i]['output_lits']

        known_literals |= set(seq[i]['output_lits'])
        i += 1

    for step in new_seq:
        step['input_lits'] = syntactic_minimize_literals(step['input_lits'])
        step['output_lits'] = syntactic_minimize_literals(step['output_lits'])

    return new_seq


def syntactic_minimize_literals(literals):
    # given two literals x <= v and x <= v + k; just keep the strongest one
    # same for >=
    # others: leave as is

    leq_map = dict()
    geq_map = dict()

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
                leq_map[lhs].add(rhs - 1)
            elif lit.name == ">=":
                if lhs not in geq_map:
                    geq_map[lhs] = set()
                geq_map[lhs].add(rhs)
            elif lit.name == ">":
                if lhs not in geq_map:
                    geq_map[lhs] = set()
                geq_map[lhs].add(rhs + 1)
            elif lit.name in ("==", "!="):
                new_literals.append(lit)
            else:
                raise ValueError("Unexpected comparison: literal", lit)
        else:
            new_literals.append(lit)

    new_literals += [var <= min(vals) for var, vals in leq_map.items()]
    new_literals += [var >= max(vals) for var, vals in geq_map.items()]

    return new_literals
