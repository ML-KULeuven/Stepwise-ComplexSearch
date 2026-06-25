import cpmpy as cp
import numpy as np


from time import time

from cpmpy.expressions.core import Expression
from .mus import MUSAlgo, WrapSolver


class OMUSEnum(MUSAlgo):

    def __init__(self, proof, constraints, mus_solver, hs_solver="gurobi"):
        super().__init__(proof, constraints, mus_solver)

        self.hs_solver = hs_solver
        self.mus_calls = dict() # metadata for each mus call performed

    def _get_val(self, item):
        if isinstance(item, Expression):
            return item.value()
        if isinstance(item, int):
            item = self.proof_dict[item]
        if isinstance(item, dict) and "derived" in item:
            return all(expr.value() for expr in item["derived"])
        raise ValueError(f"Cannot compute value of given item, expected `Expression` or proof step, but got {item}")


    def get_mus(self, soft, weights, hard, time_limit=float("inf"), step_id = None):
        start = time()

        if len(soft) == 0:
            yield []
            return

        soft_assump = self.get_assumps(soft)
        hard_assump = self.get_assumps(hard)

        assert set(soft_assump) & set(hard_assump) == set(), f"soft and hard constraints must be disjoint!"
        hs_solver = cp.SolverLookup.get(self.hs_solver)
        hs_solver.minimize(cp.sum(np.array(weights) * soft_assump))
        hs_solver = WrapSolver(hs_solver)

        # if hasattr(self.solver, "solution_hint"):
        #     self.solver.solution_hint(soft_assump, [1 for _ in soft_assump])

        hs_solver_kwargs = dict()
        if self.hs_solver == "gurobi":
            hs_solver_kwargs = dict(Threads=1)
        if self.hs_solver == "ortools":
            hs_solver_kwargs = dict(num_search_workers=1)

        if step_id is not None:
            self.mus_calls[step_id] = (dict(
                hs_solver = hs_solver,
                cons_assumps = [a for a in soft_assump if isinstance(self.dmap[a], Expression)],
                soft_assump = soft_assump,
                weights = weights
            ))


        i = 0
        while hs_solver.solve(time_limit=time_limit, **hs_solver_kwargs) is True:
            # print(f"Found hitting set with cost {hs_solver.objective_value()}")

            hs = [a for a in soft_assump if a.value()]
            # print("Found hitting set of size", hs_solver.objective_value())

            if self.solver.solve(assumptions=hs+hard_assump, time_limit=time_limit) is False:
                i += 1
                yield [self.dmap[a] for a in hs]
                hs_solver += cp.sum(hs) < len(hs) # block from being generated again

            # else SAT, find some (cheap) correction subsets
            new_corr_subset = [a for a in soft_assump if a.value() is False]
            hs_solver += cp.sum(new_corr_subset) >= 1

            # greedily search for other corr subsets disjoint to this one
            sat_subset = list(new_corr_subset)
            while self.solver.solve(assumptions=sat_subset+hard_assump, time_limit=time_limit-(time()-start)) is True:
                new_corr_subset = [a for a in soft_assump if a.value() is False]
                assert set(sat_subset) & set(new_corr_subset) == set(), "new corr subset is not disjoint to previous"
                assert len(new_corr_subset) > 0, "new corr subset is empty"
                sat_subset += new_corr_subset
                hs_solver += cp.sum(new_corr_subset) >= 1

        return