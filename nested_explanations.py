import re
import tempfile
import time
import warnings

import cpmpy as cp
from cpmpy.expressions.core import Comparison, Operator
from cpmpy.expressions.utils import flatlist
from cpmpy.transformations.normalize import toplevel_list
from cpmpy.transformations.negation import push_down_negation
from cpmpy.tools.explain.mus import mus

from proof2seq.minimize import trim_proof
from proof2seq.mus import SMUS, DeletionBasedMUS
from proof2seq.parsing import PumpkinProofParser
from proof2seq.pipeline import compute_explanation_proof, finalize_sequence
from proof2seq.utils import  print_explanation_step, get_variables


from utils import shrink_domains, lex_mus_algo, VAR_NAMES_REGEX



def get_nested_explanation_with_proof(input_lits, constraints, output_lits,
                                      time_limit=3600,
                                      proof_name="proof.drcp",
                                      mus_solver="exact",
                                      mus_algo="deletion",
                                      seed=0):
    """
        Compute a nested explanation sequence of the explanation step
            (input_lits, constraints, output_lits)
        We negate the output literals, and compute a step-wise explanation from the resulting UNSA model.
    """

    start = time.time()
    
    # normalize the input literals and constraints
    input_lits = toplevel_list(input_lits, merge_and=False)
    constraints = toplevel_list(constraints, merge_and=False)
    # negate the output literals. In practice len(output_lits) == 1, so this is just ~output_lits[0]
    neg_output = push_down_negation(toplevel_list(~cp.all(output_lits)))

    # save the original bounds of the variables, we will reset them afterwards
    _vars = get_variables(input_lits+constraints+output_lits)
    orig_bounds = {var : (var.lb, var.ub) for var in _vars}
    # propagate the input lits and negated output
    # this ensures they will be used as domains are propagated first by the solver
    shrink_domains(neg_output) # bounds are adjusted in-place!

    # compute the explanation proof using Pumpkin
    expl_proof, orig_proof = compute_explanation_proof(
                                    model=cp.Model(input_lits+constraints+neg_output),
                                    minimization_phase1="proof",
                                    minimization_phase2="proof",
                                    proof_name=proof_name,
                                    time_limit=time_limit,
                                    seed=seed)

    assert str(expl_proof[-1]['derived']) == str([cp.BoolVal(False)]), "Last step should derive False, but got" + expl_proof[-1]
    
    # reset the domains to the original ones
    for var, dom in orig_bounds.items():
        var.lb, var.ub = min(dom), max(dom)

    # trim the proof, we might lose some good nogoods,
    # but it massively reduces the size of the proof and thus simplifies minimization phase
    expl_proof = trim_proof(expl_proof)

    # initialize statefull MUS algorithm
    if mus_algo == "smus":
        mus_algo = SMUS(expl_proof, input_lits+constraints+neg_output, mus_solver=mus_solver)
    elif mus_algo == "deletion":
        mus_algo = DeletionBasedMUS(expl_proof, input_lits+constraints+neg_output, mus_solver=mus_solver)
    else:
        raise ValueError("Unknown MUS algorithm", mus_algo)

    new_proof = []
    required = {expl_proof[-1]['id']}
    nogood_dict = {step['id'] : step['derived'] for step in expl_proof}

    for step in reversed(expl_proof):
        if step['id'] not in required: 
            continue # step is not required, skip
        
        if (time.time() - start) > time_limit:
            raise TimeoutError("Time limit exceeded while computing nested explanation")

        required.remove(step['id'])

        candidate_nogoods = [x['id'] for x in expl_proof if x['id'] < step['id']]
        new_nogoods = list(set(candidate_nogoods) - set(required))
        known_nogoods = list(set(candidate_nogoods) & set(required))

        new_reasons = lex_mus_algo(mus_algo=mus_algo,
                                   lex_soft=[neg_output, input_lits, known_nogoods, new_nogoods, constraints],
                                   hard=[~cp.all(step['derived'])],
                                   time_limit=time_limit - (time.time() - start))

        step_input_lits = [r for r in new_reasons if r in set(neg_output) | set(input_lits) | set(candidate_nogoods)]
        step_constraints = [r for r in new_reasons if r in set(constraints)]

        new_proof.insert(0, dict(
            id = step['id'],
            input_lits=flatlist(nogood_dict.get(id,id) for id in step_input_lits),
            constraints=step_constraints,
            output_lits=step['derived']
        ))

        required.update(new_reasons)

    return new_proof, orig_proof

def get_first_decision_in_proof(step, already_derived_lits=[]):
    """
        So want to find the first interesting decision made by the solver.
        Interesting means:
            - it is part of the trimmed proof
            - it is on a user-level
            - ideally, it conflicts with a previously derived literal, that is not used as input for this step (unlikely to find one)
    """
    print("** Finding first decision in proof **")
    assert cp.BoolVal(False) in step['output_lits']
    model = cp.Model(step['input_lits'], step['constraints'])
    user_vars = frozenset(get_variables(model.constraints))
    # save original bounds
    orig_domains = {var: (var.lb, var.ub) for var in user_vars}
    shrink_domains(step['input_lits']) # will do so in-place
    
    # compute a proof for the step, and trim it
    prooffile = tempfile.NamedTemporaryFile(suffix=".drcp") # ensure no conflicts with parallel threads
    parser = PumpkinProofParser(model, proof=prooffile.name)
    assert parser.solve() is False
    proof = parser.read_proof_tree()
    proof = trim_proof(proof)

    # find the candidate decisions
    input_lits = frozenset(step['input_lits'])
    candidates = set()
    for proof_step in proof:
        if proof_step['type'] == 'inference' and proof_step['filtering_algorithm'] != "initial_domain":
            # format: cpmpy constraint => clause of literals
            # e.g., Alldiff(x,y,z) => x != 1 \/ y != 1; so first decision could be x = 1
            # we can pick any NEGATED literal from the clause as a first decision, but it should be a non-trivial one.
            # Additionally, it should be on a user variable!
            clause = proof_step['derived'][0]
            if isinstance(clause, Comparison): # clause with a single literal
                args = [clause]
            elif isinstance(clause, Operator) and clause.name == "or":
                args = clause.args
            else:
                raise ValueError("Unexpected derived constraint for proofstep:", proof_step['derived'])

            negated_args = push_down_negation([~arg for arg in args])
            for arg in negated_args:
                assert isinstance(arg, Comparison), f"Expected comparison literal but got {arg}"
                if arg in input_lits:
                    continue # part of the input literals, can't use this one
                if push_down_negation([~arg])[0] in input_lits:
                    continue # negation is part on the input literals, unlikely, but can't use this one either

                var, val = arg.args
                # check trivial ones
                if arg.name == "<=" and val == var.ub: continue
                if arg.name == ">=" and val == var.lb: continue
                if arg.name == "==" and var.lb == val == var.ub: continue
                if var in user_vars:
                    candidates.add(arg)

    for var, (lb, ub) in orig_domains.items():
        var.lb, var.ub = lb, ub
    if len(candidates) == 0:
        warnings.warn("No decisions were made on user variables in the proof!")
        return None, False

    already_derived_lits = list(set(already_derived_lits) - set(step['input_lits']))
    for cand in candidates: # check if there is a literal opposing one that was already derived before
        if cp.Model(already_derived_lits + [cand]).solve() is False: # massively overkill...
            if cp.Model(step['input_lits'] + [cand]).solve() is False:
                continue # highly unlikely, but it can happen...

            return cand, True # found an opposing literal

    # else, just take the first one that does not conflict the input constraints
    #   we will have to negate it as well!
    for cand in candidates:
        if cp.Model(step['input_lits'] + [cand]).solve() and cp.Model(step['input_lits'] + [~cand]).solve():
            return cand, False

    warnings.warn("Couldn't find any decision made on user variables in the proof that don't conflict the input lits")
    return None, False


def more_than_one_constraint(step):
    return len(step['constraints']) > 1

def get_nested_explanation_sequence(input_lits, constraints, output_lits,
                                    depth=0, do_nested = more_than_one_constraint, **kwargs):

    print("Computing explanation sequence at depth", depth)
    sequence, cpm_proof = get_nested_explanation_with_proof(input_lits, constraints, output_lits, **kwargs)
    sequence = finalize_sequence(sequence,
                                 extra_lits=input_lits + push_down_negation(toplevel_list(~cp.all(output_lits))))

    # we got a sequence at depth `depth`, now check every step whether it needs to be nested (further)
    new_sequence = []
    already_derived_lits = []
    for i, step in enumerate(sequence):
        if not do_nested(step): # no need for nested explanation
            new_sequence.append(step)
            print_explanation_step(step, index=i+1, indent=depth, format="literals")
            already_derived_lits += step['output_lits']
            continue
        
        # else: need to compute a nested explanation for the step
        if cp.BoolVal(False) in set(step['output_lits']):
            # edge case, last step in the sequence needs to be nested, introduce dummy
            print_explanation_step(step, index=i+1, indent=depth, format="literals")
            
            
            dummy_lit, opposed_previously_derived = get_first_decision_in_proof(step, already_derived_lits)
            if dummy_lit is None:
                step['no_nested'] = True
                new_sequence.append(step)
                already_derived_lits += step['output_lits']
                continue
            
            if opposed_previously_derived:
                # replace (input_lits, consrtaints, False) with two steps:
                # (input_lits, constraints, dummy_lit)
                # (~dummy_lit, hard=dummy_lit), [], False) # ~dummy was lit already previously in the sequence, so no need to derive it again
                step_per_lit = [dict(input_lits=step['input_lits'],
                                        constraints=step['constraints'],
                                        output_lits=[dummy_lit], id=f"{step['id']}-{dummy_lit}"),
                                dict(input_lits=mus(already_derived_lits, hard=dummy_lit),
                                        constraints=[],
                                        output_lits=[cp.BoolVal(False)],
                                        id=f"{step['id']}-False")
                                ]
            else: # replace (input_lits, consrtaints, False) with three steps:
                # (input_lits, constraints, dummy_lit)
                # (input_lits, constraints, ~dummy_lit)
                # ([dummy_lit, ~dummy_lit]), [], False)
                step_per_lit = [dict(input_lits=step['input_lits'],
                                        constraints=step['constraints'],
                                        output_lits=[dummy_lit], id=f"{step['id']}-{dummy_lit}",
                                        dummy_lit=True, oppposes_prev=False),
                                dict(input_lits=step['input_lits'],
                                        constraints=step['constraints'],
                                        output_lits=push_down_negation([~dummy_lit]), id=f"{step['id']}-{~dummy_lit}"),
                                dict(input_lits=push_down_negation([dummy_lit, ~dummy_lit]),
                                        constraints=[],
                                        output_lits=[cp.BoolVal(False)],
                                        id=f"{step['id']}-False")
                                ]
        else:
            already_derived_lits += step['output_lits']
            # Compute nested explanation for each literal in the proofstep
            step_per_lit = [dict(input_lits=step['input_lits'],
                                    constraints=step['constraints'],
                                    output_lits=[lit],
                                    id=f"{step['id']}-{lit}") for lit in step['output_lits']]

        for lstep in step_per_lit:
            new_sequence.append(lstep)
            print_explanation_step(lstep, index=i + 1, indent=depth, format="literals")

            if len(lstep['constraints']) <= 1:
                continue
            output = lstep['output_lits']

            lstep['nested_explanation'], _prf = get_nested_explanation_sequence(lstep['input_lits'],
                                                                                 lstep['constraints'],
                                                                                 output,
                                                                                 depth=depth+1,
                                                                                 **kwargs)

    return new_sequence, cpm_proof


def find_explanation_sequence(model, extra_lits=[], **algo_kwargs):
    for cpm_var in get_variables(model.constraints):
        cpm_var.name = re.sub(VAR_NAMES_REGEX, "_", cpm_var.name) # otherwise proof is not readable by external tools

    return get_nested_explanation_sequence(input_lits=extra_lits,
                                           constraints=toplevel_list(model.constraints, merge_and=False),
                                           output_lits=[cp.BoolVal(False)],
                                           **algo_kwargs)