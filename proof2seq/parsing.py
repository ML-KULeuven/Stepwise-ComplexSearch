import warnings
import gzip
import re

import cpmpy as cp
from cpmpy.expressions.utils import eval_comparison
from cpmpy.expressions.variables import _NumVarImpl, NegBoolView
from cpmpy.solvers.pumpkin import CPM_pumpkin
from cpmpy.solvers.solver_interface import ExitStatus
from cpmpy.expressions.python_builtins import any as cpm_any
from tqdm import tqdm

from .utils import normalize


RE_PROP = (r"^i\s+(?P<id>[1-9]\d*)\s+"
           r"(?P<premises>(?:-?[1-9]\d*\s*)*)"
           r"(?:0\s+(?P<propagated>-?[1-9]\d*)?\s*)?"
           r"(?:c:(?P<tag>-?[1-9]\d*))?\s*"
           r"(?:l:(?P<filtering_algorithm>\w+))?$")

RE_NOGOOD = re.compile(r"^n\s+(?P<id>-?\d+)\s+"
                       r"(?:(?P<lit_ids>(?:-?\d+\s*)*?)0\s+)?"
                       r"(?P<hint>(?:-?\d+\s*)*)")


class PumpkinProofParser(CPM_pumpkin):

    def __init__(self, model, proof=None, **kwargs):
        self._name_to_var = dict()  # DRCP var name -> CPMpy variable
        super().__init__(cpm_model=model, proof=proof, **kwargs)
        self.prefix = proof

    def solver_var(self, var):
        # Pumpkin's _varmap is name -> solver-var; we also need name -> CPMpy var
        # to rebuild expressions when parsing proof literals.
        if isinstance(var, _NumVarImpl) and not isinstance(var, NegBoolView):
            self._name_to_var[var.name] = var
        return super().solver_var(var)

    def read_proof(self, keep_step=None, prefix=None):
        """
            Parse the proof log into a list of nogood expressions.

            Only keeps steps for which ``keep_step(derived)`` returns True.
            Both nogood steps (``n``) and propagation/inference steps (``i``)
            whose derived clause passes ``keep_step`` are included.

            :param keep_step: callable(Expression) -> bool. Defaults to keeping everything.
            :param prefix: path to the proof file (defaults to the one used at construction)
            :return: list of CPMpy expressions (nogoods / derived clauses)
        """
        if keep_step is None:
            keep_step = lambda _expr: True

        if prefix is None:
            prefix = self.prefix
        assert prefix is not None, "solver has to be ran with proof-logging enabled, or prefix has to be user-supplied"

        UNSAT = False
        nogoods = []
        literals = dict()

        if prefix.endswith(".gz"):
            open_file = gzip.open(prefix, "rb")
        else:
            open_file = open(prefix, "r")

        with open_file as f:
            for line_nb, line in enumerate(tqdm(f.readlines(), desc="Parsing proof")):
                if line[0] == "a":
                    # a <id> [<var> <op> <val>]
                    a, lit_id, *lit_str = line.split(" ")
                    lit = self.parse_one_lit(" ".join(lit_str))
                    literals[int(lit_id)] = lit

                elif line[0] == "i":
                    # i <step_id> <premises> [0 <propagated>] [c:<tag>] [l:<algo>]
                    match = re.match(RE_PROP, line).groupdict()
                    lit_ids = [int(id) for id in match['premises'].split()]
                    cpm_lits = map(lambda id: literals[abs(id)], lit_ids)
                    premises = normalize([lit if id > 0 else ~lit for id, lit in zip(lit_ids, cpm_lits)])

                    if match['propagated'] is None:
                        propagated = []
                    else:
                        lit = int(match['propagated'])
                        propagated = normalize([literals[lit] if lit > 0 else ~literals[abs(lit)]])
                        assert len(propagated) == 1, f"Propagated should be a single literal, got {propagated}"

                    derived = cpm_any(normalize([~lit for lit in premises] + propagated))
                    if keep_step(derived):
                        nogoods.append(derived)

                elif line[0] == "n":
                    # n <step_id> <atomic ids> [0 <hint step ids>]
                    match = re.match(RE_NOGOOD, line).groupdict()
                    lit_ids = [int(id) for id in match['lit_ids'].strip().split()] if match['lit_ids'] else []

                    cpm_lits = map(lambda id: literals[abs(id)], lit_ids)
                    premises = [lit if id > 0 else ~lit for id, lit in zip(lit_ids, cpm_lits)]

                    if len(premises) == 0:
                        derived = cp.BoolVal(False)
                        UNSAT = True  # empty nogood concludes unsatisfiability
                    else:
                        derived = cpm_any(normalize([~lit for lit in premises]))

                    if keep_step(derived):
                        nogoods.append(derived)

                elif line[0] == "c": # reached conclusion
                    # c UNSAT  OR  c <objective bound>
                    if line.strip() == "c UNSAT":
                        UNSAT = True
                    break

        if not UNSAT and self.status().exitstatus == ExitStatus.UNSATISFIABLE:
            warnings.warn(
                f"Expected the proof to be a proof of unsatisfiability, but got {line!r} as last proofstep\n"
                "Adding BoolVal(False) at the end"
            )
            if keep_step(cp.BoolVal(False)):
                nogoods.append(cp.BoolVal(False))

        # drop duplicate expressions, preserving order
        seen = set()
        unique = []
        for ng in nogoods:
            key = str(ng)
            if key in seen:
                continue
            seen.add(key)
            unique.append(ng)
        return unique

    def parse_one_lit(self, string):
        """
            Parse one literal.
            A literal is a comparison of a variable with an integer.
            Allowed comparisons are "==", "!=", "<=", ">="
        """
        string = string.strip().strip(" []")

        if "true" in string:
            return True

        for comp in ("!=", "<=", ">=", "=="):
            if comp in string:
                break
        else:
            raise ValueError(f"Expected comparison but got {string}")

        lhs, rhs = string.split(comp)
        lhs, rhs = lhs.strip(), int(rhs.strip())

        if lhs not in self._name_to_var:
            raise ValueError(f"Unknown literal {string}, could not find '{lhs}' in name_to_var map")

        return eval_comparison(comp, self._name_to_var[lhs], rhs)
