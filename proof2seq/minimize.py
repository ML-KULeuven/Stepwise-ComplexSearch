import copy
from time import time

import cpmpy as cp
from cpmpy.expressions.core import Expression
from cpmpy.transformations.normalize import toplevel_list

from .mus import DeletionBasedMUS, SMUS


def minimize_proof(proof, model, minimization_type="global", mus_type="smus", verbose=0, time_limit=None, **mus_algo_kwargs):

    assert minimization_type in {"proof", "trim", "local", "global"}
    start = time()

    if minimization_type == "proof":
        return proof # do nothing

    if minimization_type == "trim":
        return trim_proof(proof)

    if mus_type == "mus":
        mus_algo = DeletionBasedMUS(proof, model.constraints, **mus_algo_kwargs)
    elif mus_type == "smus":
        mus_algo = SMUS(proof, model.constraints, **mus_algo_kwargs)
    else:
        raise ValueError(f"Unknown MUS type {mus_type}, expected 'mus' or 'smus'")


    required = {proof[-1]['id']}
    new_proof = []

    if verbose >= 3:
        print(f"Minimizing proof with {len(proof)} steps")
    for step in reversed(proof):
        if time_limit is not None and (time() - start) > time_limit:
            raise TimeoutError("Time limit exceeded while minimizing proof")

        if step['id'] in required:
            if verbose >= 3:
                print("Minimizing proof step", step['id'])
            # Step is required, let's minimize the reasons of this step
            # We want a MUS that minimizes the number of constraints
            # Additionally, we prefer nogoods that we need to explain already anyway
            # Hence, we have a 3-step approach to achieve this, using 3 MUS calls

            if minimization_type == "local":
                candidate_nogoods = [r for r in step['reasons'] if isinstance(r, int)]
                candidate_cons = [r for r in step['reasons'] if isinstance(r, Expression)]
                assert len(candidate_nogoods) + len(candidate_cons) == len(step['reasons']), "Euhm something went wrong here..."

            if minimization_type == "global":
                candidate_nogoods = [x['id'] for x in proof if x['type'] == 'nogood' and x['id'] < step['id']]
                candidate_cons = toplevel_list(model.constraints, merge_and=False)

            # Minimize number of constraints
            if verbose >= 4:
                print(f"Computing required constraints (out of {len(candidate_cons)})")
            required_cons = mus_algo.get_mus(soft=candidate_cons,
                                             hard=candidate_nogoods + [~cp.all(step['derived'])],
                                             time_limit= time_limit)

            # Minimize number of nogoods
            potential_known_nogoods = [r for r in candidate_nogoods if r in required]
            potential_new_nogoods = [r for r in candidate_nogoods if r not in required]

            if verbose >= 4:
                print(f"Computing required new nogoods (out of {len(potential_new_nogoods)})")
            required_new_nogoods = mus_algo.get_mus(soft=potential_new_nogoods,
                                                    hard=potential_known_nogoods + required_cons + [~cp.all(step['derived'])],
                                                    time_limit= time_limit)

            if verbose >= 4:
                print(f"Computing required new nogoods (out of {len(potential_new_nogoods)})")
            required_known_nogoods = mus_algo.get_mus(soft=potential_known_nogoods,
                                                      hard=required_new_nogoods + required_cons + [~cp.all(step['derived'])],
                                                      time_limit = time_limit)

            required_nogoods = required_new_nogoods + required_known_nogoods
            assert all(isinstance(ng, int) for ng in required_nogoods)

            # Update set of required steps
            required.update(required_nogoods)
            new_reasons = required_cons + required_nogoods


            if verbose >= 3:
                print(f"Done with minimization of proof step {step['id']}, reduced number of reasons from {len(step['reasons'])} to {len(new_reasons)}")

            step = copy.copy(step)
            step['reasons'] = new_reasons
            new_proof.insert(0, step)

    return new_proof





def trim_proof(proof):
    # work from back to front
    required = {proof[-1]['id']}
    new_proof = []
    for step in reversed(proof):
        if step['id'] in required:
            new_proof.insert(0, step)
            required.update(step['reasons'])
    return new_proof
