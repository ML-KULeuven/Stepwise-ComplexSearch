"""
    Stateful implementation of MUS-algorithms present in CPMPy

    Soft/hard inputs are CPMpy Expressions. When a new soft/hard constraint is
    passed that is not yet registered, a fresh indicator variable is created and
    the assumption maps are updated.
"""
from __future__ import annotations

from time import time
from typing import Iterable, Iterator

import cpmpy as cp
from cpmpy.solvers.solver_interface import ExitStatus, SolverInterface
from cpmpy.tools.explain.utils import make_assump_model
from cpmpy.expressions.core import Expression
from cpmpy.expressions.variables import _BoolVarImpl
from cpmpy.transformations.normalize import toplevel_list

from .utils import get_variables


class WrapSolver(SolverInterface):

    def __init__(self, cpm_solver: SolverInterface):
        assert isinstance(cpm_solver, SolverInterface)
        self.cpm_solver = cpm_solver

    def solve(self, *args, time_limit: float | None = None, **kwargs) -> bool:
        if time_limit is not None and time_limit <= 0:
            raise TimeoutError("Solver timed out")

        res = self.cpm_solver.solve(*args, time_limit=time_limit, **kwargs)
        status = self.cpm_solver.status().exitstatus
        if status in {ExitStatus.FEASIBLE, ExitStatus.OPTIMAL, ExitStatus.UNSATISFIABLE}:
            return res
        if status == ExitStatus.UNKNOWN:
            raise TimeoutError("Solver timed out")
        raise ValueError(f"Solver returned unknown status {status}")

    def add(self, *args, **kwargs) -> WrapSolver:
        self.cpm_solver.add(*args, **kwargs)
        return self

    def __add__(self, *args, **kwargs) -> WrapSolver:
        self.cpm_solver.__add__(*args, **kwargs)
        return self

    def get_core(self) -> list[_BoolVarImpl]:
        return self.cpm_solver.get_core()

    def objective(self, *args, **kwargs):
        return self.cpm_solver.objective(*args, **kwargs)

    def objective_value(self, *args, **kwargs):
        return self.cpm_solver.objective_value(*args, **kwargs)


class MUSAlgo:

    cons: list[Expression]
    assump: list[_BoolVarImpl]
    dmap: dict[_BoolVarImpl, Expression]
    rev_map: dict[Expression, _BoolVarImpl]
    solver: WrapSolver

    def __init__(self, constraints: Iterable[Expression], mus_solver: str):
        """
        Initialize the MUS algorithm over a pool of (soft) constraints.

        :param constraints: iterable of CPMpy Expressions to register up-front
        :param mus_solver: name of the underlying CPMpy solver
        """
        constraints = toplevel_list(constraints, merge_and=False)
        assump_model, self.cons, self.assump = make_assump_model(constraints)
        self.assump = list(self.assump)
        self.cons = list(self.cons)

        self.dmap = dict(zip(self.assump, self.cons))       # indicator -> constraint
        self.rev_map = dict(zip(self.cons, self.assump))    # constraint -> indicator

        solver = cp.SolverLookup.get(mus_solver, assump_model)
        self.solver = WrapSolver(solver)

    def get_mus(
        self,
        soft: list[Expression],
        hard: list[Expression],
        time_limit: float | None = None,
    ) -> list[Expression]:
        raise NotImplementedError

    def get_assumps(self, lst: Iterable[Expression]) -> list[_BoolVarImpl]:
        """
        Map soft/hard items to their indicator variables.
        Unknown Expressions get a fresh indicator; the assumption maps are updated.
        """
        assumps = []
        for x in lst:
            if str(x) == str(cp.BoolVal(True)):
                continue
            if x not in self.rev_map:
                assert isinstance(x, Expression), f"Expected Expression, got {type(x)}: {x}"
                bv = cp.boolvar()
                self.solver += bv.implies(x)
                self.assump.append(bv)
                self.cons.append(x)
                self.rev_map[x] = bv
                self.dmap[bv] = x
                assumps.append(bv)
            else:
                assumps.append(self.rev_map[x])

        return assumps


class DeletionBasedMUS(MUSAlgo):

    def get_mus(
        self,
        soft: list[Expression],
        hard: list[Expression],
        time_limit: float | None = None,
    ) -> list[Expression]:

        soft_assump = self.get_assumps(soft)
        hard_assump = self.get_assumps(hard)

        assert self.solver.solve(assumptions=soft_assump + hard_assump, time_limit=time_limit) is False

        core = set(self.solver.get_core()) - set(hard_assump)
        for c in sorted(core, key=lambda c: -len(get_variables(self.dmap[c]))):
            if c not in core:
                continue
            core.remove(c)
            if self.solver.solve(assumptions=list(core) + hard_assump, time_limit=time_limit) is True:
                core.add(c)
            else:
                core = set(self.solver.get_core()) - set(hard_assump)

        return [self.dmap[a] for a in core]


class SMUS(MUSAlgo):

    def __init__(
        self,
        constraints: Iterable[Expression],
        mus_solver: str,
        hs_solver: str = "gurobi",
    ):
        super().__init__(constraints, mus_solver)
        self.hs_solver = hs_solver

    def get_mus(
        self,
        soft: list[Expression],
        hard: list[Expression],
        time_limit: float | None = None,
    ) -> list[Expression]:

        if len(soft) == 0:
            return soft

        soft_assump = self.get_assumps(soft)
        if len(soft_assump) == 0:
            return []
        hard_assump = self.get_assumps(hard)

        assert set(soft_assump) & set(hard_assump) == set(), "soft and hard constraints must be disjoint!"
        hs_solver = cp.SolverLookup.get(self.hs_solver)
        hs_solver.minimize(cp.sum(soft_assump))
        hs_solver = WrapSolver(hs_solver)

        hs_solver_kwargs = dict()
        if self.hs_solver == "gurobi":
            hs_solver_kwargs = dict(Threads=1)
        if self.hs_solver == "ortools":
            hs_solver_kwargs = dict(num_search_workers=1)

        while hs_solver.solve(time_limit=time_limit, **hs_solver_kwargs) is True:

            hs = [a for a in soft_assump if a.value()]

            if self.solver.solve(assumptions=hs + hard_assump, time_limit=time_limit) is False:
                return [self.dmap[a] for a in hs]

            new_corr_subset = [a for a in soft_assump if a.value() is False]
            hs_solver += cp.sum(new_corr_subset) >= 1

            sat_subset = list(new_corr_subset)
            while self.solver.solve(assumptions=sat_subset + hard_assump, time_limit=time_limit) is True:
                new_corr_subset = [a for a in soft_assump if a.value() is False]
                assert set(sat_subset) & set(new_corr_subset) == set(), (
                    f"new corr subset is not disjoint to previous\n"
                    f"{[self.dmap[a] for a in set(sat_subset) & set(new_corr_subset)]}"
                )
                assert len(new_corr_subset) > 0, "new corr subset is empty"
                sat_subset += new_corr_subset
                hs_solver += cp.sum(new_corr_subset) >= 1

        raise ValueError("HS solver is UNSAT, this should not happen!")


class Marco(MUSAlgo):

    def __init__(
        self,
        constraints: Iterable[Expression],
        mus_solver: str,
        map_solver: str = "pysat",
    ):
        super().__init__(constraints, mus_solver)
        self.map_solver = map_solver

    def get_mus(
        self,
        soft: list[Expression],
        hard: list[Expression],
        max_musses: float = float("inf"),
        time_limit: float = float("inf"),
    ) -> Iterator[list[Expression]]:
        start = time()

        if len(soft) == 0:
            return

        soft_assump = self.get_assumps(soft)
        hard_assump = self.get_assumps(hard)

        assert self.solver.solve(
            assumptions=soft_assump + hard_assump,
            time_limit=time_limit - (time() - start),
        ) is False

        assert set(soft_assump) & set(hard_assump) == set(), "soft and hard constraints must be disjoint!"
        map_solver = WrapSolver(cp.SolverLookup.get(self.map_solver))

        map_solver += cp.any(soft_assump) | cp.boolvar()
        map_solver.cpm_solver.solution_hint(soft_assump, [1 for _ in soft_assump])

        n_musses = 0
        while n_musses < max_musses and map_solver.solve() is True:

            hs = [a for a in soft_assump if a.value()]

            if self.solver.solve(
                assumptions=hs + hard_assump,
                time_limit=time_limit - (time() - start),
            ) is False:
                core = set(self.solver.get_core()) - set(hard_assump)
                for c in sorted(core, key=lambda c: -len(get_variables(self.dmap[c]))):
                    if c not in core:
                        continue
                    core.remove(c)
                    if self.solver.solve(
                        assumptions=list(core) + hard_assump,
                        time_limit=time_limit - (time() - start),
                    ) is True:
                        core.add(c)
                    else:
                        core = set(self.solver.get_core()) - set(hard_assump)
                n_musses += 1
                yield [self.dmap[a] for a in core]
                map_solver += ~cp.all(core)
            else:
                new_corr_subset = [a for a in soft_assump if a.value() is False]
                map_solver += cp.any(new_corr_subset)


def _quickxplain_recurse(
    solver: WrapSolver,
    soft: list[_BoolVarImpl],
    hard: list[_BoolVarImpl],
    hard_assump: list[_BoolVarImpl],
    delta: list[_BoolVarImpl],
) -> list[_BoolVarImpl]:
    if len(delta) != 0 and solver.solve(assumptions=hard + hard_assump) is False:
        return []

    if len(soft) == 1:
        return list(soft)

    split = len(soft) // 2
    more_preferred, less_preferred = soft[:split], soft[split:]

    delta2 = _quickxplain_recurse(solver, less_preferred, hard + more_preferred, hard_assump, more_preferred)
    delta1 = _quickxplain_recurse(solver, more_preferred, hard + delta2, hard_assump, delta2)
    return delta1 + delta2


class QuickXplain(MUSAlgo):

    def get_mus(
        self,
        soft: list[Expression],
        hard: list[Expression],
        time_limit: float | None = None,
    ) -> list[Expression]:

        soft_assump = self.get_assumps(soft)
        hard_assump = self.get_assumps(hard)

        assert self.solver.solve(assumptions=soft_assump + hard_assump) is False, "The model should be UNSAT!"

        solver_core = frozenset(self.solver.get_core())
        max_idx = max(i for i, a in enumerate(soft_assump) if a in solver_core)

        core = _quickxplain_recurse(
            self.solver, list(soft_assump)[:max_idx + 1], [], hard_assump, [],
        )
        return [self.dmap[a] for a in core]
