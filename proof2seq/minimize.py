from __future__ import annotations

from time import time

from cpmpy.expressions.core import Expression
from cpmpy.transformations.normalize import toplevel_list

from .mus import DeletionBasedMUS, SMUS, MUSAlgo, QuickXplain


def minimize_proof(
    nogoods: list[Expression],
    constraints: list[Expression],
    mus_type: str = "smus",
    time_limit: float | None = None,
    mus_algo: MUSAlgo | None = None,
    **mus_algo_kwargs,
) -> list[Expression]:
    """
    Globally minimize a list of nogood expressions by walking backwards from
    the last nogood. For each required conclusion, prefer fewer model
    constraints, then fewer newly introduced nogoods, then already-required ones.
    Candidates are all earlier nogoods plus the model constraints.

    :param nogoods: starting proof (list of CPMpy Expressions)
    :param constraints: model constraints
    :return: minimized list of nogood Expressions (order preserved)
    """
    start = time()
    constraints = toplevel_list(constraints, merge_and=False)
    nogoods = list(nogoods)

    if len(nogoods) == 0:
        return nogoods

    if mus_algo is None:
        if mus_type == "mus":
            mus_algo = DeletionBasedMUS(constraints + nogoods, **mus_algo_kwargs)
        elif mus_type == "smus":
            mus_algo = SMUS(constraints + nogoods, **mus_algo_kwargs)
        elif mus_type == "quickxplain":
            mus_algo = QuickXplain(constraints + nogoods, **mus_algo_kwargs)
        else:
            raise ValueError(f"Unknown MUS type {mus_type}, expected 'mus', 'smus', or 'quickxplain'")

    required = {len(nogoods) - 1}
    kept = []

    for i in reversed(range(len(nogoods))):
        if time_limit is not None and (time() - start) > time_limit:
            raise TimeoutError("Time limit exceeded while minimizing proof")

        if i not in required:
            continue

        derived = nogoods[i]

        candidate_nogoods = nogoods[:i]
        candidate_cons = constraints

        required_cons = mus_algo.get_mus(
            soft=candidate_cons,
            hard=candidate_nogoods + [~derived],
            time_limit=time_limit,
        )

        potential_known = [nogoods[j] for j in range(i) if j in required]
        potential_new = [nogoods[j] for j in range(i) if j not in required]

        required_new = mus_algo.get_mus(
            soft=potential_new,
            hard=potential_known + required_cons + [~derived],
            time_limit=time_limit,
        )

        required_known = mus_algo.get_mus(
            soft=potential_known,
            hard=required_new + required_cons + [~derived],
            time_limit=time_limit,
        )

        needed = required_new + required_known
        for j in range(i):
            if nogoods[j] in needed:
                required.add(j)

        kept.insert(0, derived)

    return kept
