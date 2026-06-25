"""
    Stateful implementation of MUS-algorithms present in CPMPy
"""
from time import time

import cpmpy as cp
from cpmpy.solvers.solver_interface import ExitStatus, SolverInterface
from cpmpy.tools.explain.utils import make_assump_model
from cpmpy.expressions.core import Expression
import numpy as np

import proof2seq
from .utils import get_variables

class WrapSolver(SolverInterface):

    def __init__(self, cpm_solver: SolverInterface):
        assert isinstance(cpm_solver, SolverInterface)
        self.cpm_solver = cpm_solver

        # print("Initialized wrapped solver instance for", self.cpm_solver.name)

    def solve(self, *args, time_limit=None, **kwargs):

        if time_limit is not None and proof2seq.START_TIME is not None:
            time_limit = time_limit - (time() - proof2seq.START_TIME)
        if time_limit is not None and time_limit <= 0:
            raise TimeoutError("Solver timed out")

        res = self.cpm_solver.solve(*args,time_limit=time_limit, **kwargs)
        status = self.cpm_solver.status().exitstatus
        if status in {ExitStatus.FEASIBLE, ExitStatus.OPTIMAL, ExitStatus.UNSATISFIABLE}:
            return res
        if status == ExitStatus.UNKNOWN:
            raise TimeoutError("Solver timed out")
        raise ValueError(f"Solver returned unknown status {status}")

    def add(self, *args, **kwargs):
        self.cpm_solver.add(*args, **kwargs)
        return self
    def __add__(self, *args, **kwargs):
        self.cpm_solver.__add__(*args, **kwargs)
        return self

    def get_core(self):
        return self.cpm_solver.get_core()
    def objective(self, *args, **kwargs):
        return self.cpm_solver.objective(*args, **kwargs)
    # def solution_hint(self, *args, **kwargs):
        return self.cpm_solver.solution_hint(*args, **kwargs)
    def objective_value(self, *args, **kwargs):
        return self.cpm_solver.objective_value(*args, **kwargs)


class MUSAlgo:

    def __init__(self, proof, constraints, mus_solver):
        """
        Initialize the MUS algorithm.
        :param proof:
        :param constraints:
        :param solver:
        """
        assump_model, self.cons, self.assump = make_assump_model(constraints)
        self.assump = list(self.assump)

        self.proof_dict = {step['id'] : step for step in proof}

        # now add the derived constraints in the proof too
        for step in proof:
            # if step['type'] != "nogood":
            #     raise ValueError(f"expected only nogoods in proof, inference reasons should have been replace already\n"
            #                      f"got step {step} of type '{step['type']}'")
            bv = cp.boolvar()
            self.assump.append(bv)
            self.cons.append(step['id'])
            assump_model += bv.implies(cp.all(step['derived']))

        self.dmap = dict(zip(self.assump, self.cons))
        self.rev_map = dict(zip(self.cons, self.assump))

        solver = cp.SolverLookup.get(mus_solver, assump_model)
        self.solver = WrapSolver(solver)

    def get_mus(self, soft, hard, time_limit=None):
        raise NotImplementedError

    def get_assumps(self, lst):

        assumps = []
        for x in lst:
            if str(x) == str(cp.BoolVal(True)): continue
            if x not in self.rev_map:
                assert isinstance(x, Expression)
                bv = cp.boolvar()
                self.solver += bv.implies(x)
                self.rev_map[x] = bv
                self.dmap[bv] = x
                assumps.append(bv)
            else:
                assumps.append(self.rev_map[x])

        return assumps

class DeletionBasedMUS(MUSAlgo):

    def get_mus(self, soft, hard, time_limit=None):

        soft_assump = self.get_assumps(soft)
        hard_assump = self.get_assumps(hard)

        assert self.solver.solve(assumptions=soft_assump+hard_assump, time_limit=time_limit) is False

        core = set(self.solver.get_core()) - set(hard_assump)
        for c in sorted(core, key=lambda c: -len(get_variables(self.dmap[c]))):
            if c not in core:
                continue  # already removed
            core.remove(c)
            if self.solver.solve(assumptions=list(core) + hard_assump, time_limit=time_limit) is True:
                core.add(c)
            else:  # UNSAT, use new solver core (clause set refinement)
                core = set(self.solver.get_core()) - set(hard_assump)

        return [self.dmap[a] for a in core]

class SMUS(MUSAlgo):

    def __init__(self, proof, constraints, mus_solver, hs_solver="gurobi"):
        super().__init__(proof, constraints, mus_solver)

        self.hs_solver = hs_solver

    def _get_val(self, item):
        if isinstance(item, Expression):
            return item.value()
        if isinstance(item, int):
            item = self.proof_dict[item]
        if isinstance(item, dict) and "derived" in item:
            return all(expr.value() for expr in item["derived"])
        raise ValueError(f"Cannot compute value of given item, expected `Expression` or proof step, but got {item}")


    def get_mus(self, soft, hard, time_limit=None):

        if len(soft) == 0:
            return soft

        soft_assump = self.get_assumps(soft)
        if len(soft_assump) == 0:
            return []
        hard_assump = self.get_assumps(hard)

        # assert self.solver.solve(assumptions=soft_assump+hard_assump, time_limit=time_limit) is False, "Input model is not UNSAT!"

        assert set(soft_assump) & set(hard_assump) == set(), f"soft and hard constraints must be disjoint!"
        hs_solver = cp.SolverLookup.get(self.hs_solver)
        hs_solver.minimize(cp.sum(soft_assump))
        hs_solver = WrapSolver(hs_solver)

        # if hasattr(self.solver, "solution_hint"):
        #     self.solver.solution_hint(soft_assump, [1 for _ in soft_assump])

        hs_solver_kwargs = dict()
        if self.hs_solver == "gurobi":
            hs_solver_kwargs = dict(Threads=1)
        if self.hs_solver == "ortools":
            hs_solver_kwargs = dict(num_search_workers=1)

        while hs_solver.solve(time_limit=time_limit, **hs_solver_kwargs) is True:

            hs = [a for a in soft_assump if a.value()]

            if self.solver.solve(assumptions=hs+hard_assump, time_limit=time_limit) is False:
                # UNSAT, found MUS
                return [self.dmap[a] for a in hs]

            # else SAT, find some (cheap) correction subsets
            new_corr_subset = [a for a in soft_assump if a.value() is False]
            hs_solver += cp.sum(new_corr_subset) >= 1

            # greedily search for other corr subsets disjoint to this one
            sat_subset = list(new_corr_subset)
            while self.solver.solve(assumptions=sat_subset+hard_assump, time_limit=time_limit) is True:
                new_corr_subset = [a for a in soft_assump if a.value() is False]
                assert set(sat_subset) & set(new_corr_subset) == set(), f"new corr subset is not disjoint to previous\n{[self.dmap[a] for a in set(sat_subset) & set(new_corr_subset)]}"
                assert len(new_corr_subset) > 0, "new corr subset is empty"
                sat_subset += new_corr_subset
                hs_solver += cp.sum(new_corr_subset) >= 1

        raise ValueError("HS solver is UNSAT, this should not happen!")



class Marco(MUSAlgo):

    def __init__(self, proof, constraints, mus_solver, map_solver="pysat"):
        super().__init__(proof, constraints, mus_solver)

        self.map_solver = map_solver

    def get_mus(self, soft, hard, max_musses=float("inf"), time_limit=float("inf")):

        start = time()

        if len(soft) == 0:
            return soft

        soft_assump = self.get_assumps(soft)
        hard_assump = self.get_assumps(hard)

        assert self.solver.solve(assumptions=soft_assump+hard_assump, time_limit=time_limit-(time()-start)) is False

        assert set(soft_assump) & set(hard_assump) == set(), f"soft and hard constraints must be disjoint!"
        map_solver = cp.SolverLookup.get(self.map_solver)
        map_solver = WrapSolver(map_solver)

        map_solver += cp.any(soft_assump) | cp.boolvar() # add dummy boolvar for triival musses (in hard cons)

        map_solver.cpm_solver.solution_hint(soft_assump, [1 for _ in soft_assump])

        n_musses = 0
        while n_musses < max_musses and map_solver.solve() is True:

            hs = [a for a in soft_assump if a.value()]

            if self.solver.solve(assumptions=hs + hard_assump, time_limit=time_limit-(time()-start)) is False:
                print("UNSAT, shrink")
                # UNSAT, shrink to true MUS
                core = set(self.solver.get_core()) - set(hard_assump)
                for c in sorted(core, key=lambda c: -len(get_variables(self.dmap[c]))):
                    if c not in core:
                        continue  # already removed
                    core.remove(c)
                    if self.solver.solve(assumptions=list(core) + hard_assump,
                                         time_limit=time_limit - (time() - start)) is True:
                        core.add(c)
                    else:  # UNSAT, use new solver core (clause set refinement)
                        core = set(self.solver.get_core()) - set(hard_assump)
                n_musses += 1
                yield [self.dmap[a] for a in core]

                map_solver += ~cp.all(core) # generate a different one next time


            else:
                print("SAT, grow")
                # SAT, grow to MSS (not actually, just take the complement)
                new_corr_subset = [a for a in soft_assump if a.value() is False]
                map_solver += cp.any(new_corr_subset)

class QuickXplain(MUSAlgo):

    def get_mus(self, soft, hard, time_limit=None):

        soft_assump = self.get_assumps(soft)
        hard_assump = self.get_assumps(hard)

        assert self.solver.solve(assumptions=soft_assump+hard_assump) is False, "The model should be UNSAT!"

        # the recursive call
        def do_recursion(soft, hard, delta):

            if len(delta) != 0 and self.solver.solve(assumptions=hard+hard_assump) is False:
                # conflict is in hard constraints, no need to recurse
                return []

            if len(soft) == 1:
                # conflict is not in hard constraints, but only 1 soft constraint
                return list(soft)  # base case of recursion

            split = len(soft) // 2  # determine split point
            more_preferred, less_preferred = soft[:split], soft[split:]  # split constraints into two sets

            # treat more preferred part as hard and find extra constants from less preferred
            delta2 = do_recursion(less_preferred, hard + more_preferred, more_preferred)
            # find which preferred constraints exactly
            delta1 = do_recursion(more_preferred, hard + delta2, delta2)
            return delta1 + delta2

        # optimization: find max index of solver core
        solver_core = frozenset(self.solver.get_core())
        max_idx = max(i for i, a in enumerate(soft_assump) if a in solver_core)

        core = do_recursion(list(soft_assump)[:max_idx + 1], [], [])
        return [self.dmap[a] for a in core]











