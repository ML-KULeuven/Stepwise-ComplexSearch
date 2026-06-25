import numpy as np

import cpmpy as cp

from cpmpy.expressions.core import Expression, Operator, Comparison, BoolVal
from cpmpy.expressions.variables import _BoolVarImpl, NegBoolView, _NumVarImpl
from cpmpy.expressions.utils import is_num

from cpmpy.transformations.get_variables import get_variables as cpm_get_variables
from cpmpy.transformations.negation import push_down_negation
from cpmpy.expressions.utils import flatlist
from natsort import natsorted


def to_list_recursive(lst):
    if isinstance(lst, (list, set, frozenset, tuple, np.ndarray)):
        return [to_list_recursive(v) for v in lst]
    return lst

def get_variables(constraints):
    """
    Helper function to get variables in collection of constraints
    Accepts any (nested) iterator as input
    """
    return cpm_get_variables(to_list_recursive(constraints))

def normalize(lst_of_exprs):
    """
        Normalize a list of CPMpy expressions.
        Will transform any < to <= and > to >=.
        Output is guaranteed to be a list Comparisons or BoolVal (no NegBoolView or _BoolVarImpl)
    """
    newlst = []
    for cpm_expr in push_down_negation(lst_of_exprs):

        if isinstance(cpm_expr, Operator) and cpm_expr.name == "or":
            newlst.append(cp.any(normalize(cpm_expr.args)))

        elif isinstance(cpm_expr, NegBoolView):
            newlst.append(cpm_expr._bv <= 0)

        elif isinstance(cpm_expr, _BoolVarImpl):
            newlst.append(cpm_expr >= 1)

        elif isinstance(cpm_expr, BoolVal):
            newlst.append(cpm_expr)

        elif isinstance(cpm_expr, Comparison):
            lhs, rhs = cpm_expr.args
            assert isinstance(lhs, _NumVarImpl) and is_num(rhs), f"Expected comparison to be canonical, but got {cpm_expr}"
            if cpm_expr.name == "<":
                newlst.append(lhs <= rhs - 1)
            elif cpm_expr.name == ">":
                newlst.append(lhs >= rhs + 1)
            else:  # other comparisons are fine
                newlst.append(cpm_expr)
        else:
            raise ValueError(f"Unexpected expression: {cpm_expr}")

    return sorted(newlst, key=str)  # , key=lambda x : x.args[0].name)

def get_cpm_reasons(step, proof):

    if isinstance(proof, list):
        proof = {step['id'] for step in proof}

    cpm_reasons = []
    for used in step['reasons']:
        if isinstance(used, int): # it's a step id
            cpm_reasons.append(proof[used]['derived'])
        else:
            assert isinstance(used, Expression), f"Expected int or expression but got {used}"
            cpm_reasons.append(used)
    return cpm_reasons

def sanity_check_proof(proof):

    proof_dict = {step['id'] : step for step in proof}
    for step in proof:
        # check all used steps have a smaller id
        for r in step['reasons']:
            if isinstance(r, int) and r >= step['id']:
                raise ValueError(f"Proof step {step} uses steps that occur later in the proof!\n{step['reasons']}")

        if len(set(step['reasons'])) != len(step['reasons']):
            raise ValueError(f"Duplicate reason in step {step}")

        # check output is logically implied by input
        cpm_reasons = get_cpm_reasons(step, proof_dict)
        cpm_derived = step['derived']

        for cons in cpm_derived:
            if not isinstance(cons, Expression):
                raise ValueError(f"Expected expression, got {cons} in proof step {step}")


        unsat_model = cp.Model(cpm_reasons + [~cp.all(cpm_derived)])
        if unsat_model.solve() is not False:
            print(step)
            raise ValueError(f"Error in proof step with id {step['id']}!\n"
                             f"Reasons do not logically imply derived constraint!\n"
                             f"Reasons:\n\t" +'\n\t'.join(map(str,cpm_reasons)) +"\n"
                             f"Derived: {cpm_derived}")

def sanity_check_sequence(seq):

    current_lits = []
    for step in seq:

        assert set(step['input_lits']) <= frozenset(current_lits)
        assert cp.Model(step['input_lits'] + step['constraints'] + [~cp.all(step['output_lits'])]).solve() is False
        current_lits = list(set(current_lits) | set(step['output_lits']))


def get_proof_statistics(proof):
    n_reasons = [len(step['reasons']) for step in proof]
    n_cons = [sum(isinstance(r,Expression) for r in step['reasons']) for step in proof]
    return dict(
        length = len(proof),
        avg_reasons = sum(n_reasons) / len(n_reasons),
        std_reasons = np.std(n_reasons),
        max_reasons = max(n_reasons),
        max_cons = max(n_cons),
        avg_cons = sum(n_cons) / len(proof)
    )

def print_proof_statistics(proof, name="Proof", precision=2):

    print(f"Statistics for {name}:")
    stats = get_proof_statistics(proof)
    print("#steps:", stats['length'], end="\t")
    print("avg #reasons:", round(stats['avg_reasons'],precision), end="\t")
    print("std #reasons:", round(stats['std_reasons'], precision), end="\t")
    print("max #reasons:", stats['max_reasons'], end="\t")
    print("max #constraints:", stats['max_cons'], end="\t")
    print("avg #constraints:", round(stats['avg_cons'],precision), end="\t")
    print("\n")

def get_sequence_statistics(sequence):

    n_cons = [len(step['constraints']) for step in sequence]
    return dict(
        length = len(sequence),
        avg_cons = sum(n_cons) / len(sequence),
        std_cons = np.std(n_cons),
        max_cons = max(n_cons)
    )

def print_sequence_statistics(sequence, precision=2):

    print("Statistics for explanation sequence:")
    stats = get_sequence_statistics(sequence)
    print("#steps:", stats['length'], end="\t")
    print("avg #constraints:", round(stats['avg_cons'],precision), end="\t")
    print("std #constraints:", round(stats['std_cons'], precision), end="\t")
    print("max #constraints:", stats['max_cons'], end="\t")
    print("\n")


from cpmpy.transformations.normalize import toplevel_list
def get_domains_from_literals(literals):
    domains = dict()
    for lit in push_down_negation(toplevel_list(literals)):
        if isinstance(lit, BoolVal):
            if lit.value() is False:
                return [lit]
        elif isinstance(lit, Comparison):
            var, val = lit.args
            assert is_num(val), f"Expected atomic constraint but got {lit}"
            if var not in domains:
                domains[var] = set(range(var.lb, var.ub + 1))
            if lit.name == "==":
                domains[var] &= {val}
            elif lit.name == "!=":
                domains[var] -= {val}
            elif lit.name == ">=":
                domains[var] -= set(range(var.lb, val))
            elif lit.name == ">":
                domains[var] -= set(range(var.lb, val + 1))
            elif lit.name == "<=":
                domains[var] -= set(range(val + 1, var.ub + 1))
            elif lit.name == "<":
                domains[var] -= set(range(val, var.ub + 1))
            else:
                raise ValueError(f"Unexpected comparison {lit.name}")
        elif isinstance(lit, Operator) and lit.name == "or" and len(get_variables(lit)) == 1:
            var = get_variables(lit)[0]
            if var not in domains:
                domains[var] = set(range(var.lb, var.ub + 1))
            or_domains = [get_domains_from_literals([arg]) for arg in lit.args]
            domains[var] &= set().union(*[dom[var] for dom in or_domains])
        else:
            raise ValueError(f"Unexpected literal {lit}")
    return domains


from itertools import groupby

def split_to_nonconsequetive(lst, key=None):
    parts = []
    for _, g in groupby(enumerate(sorted(lst, key=key)), lambda x: x[0] - x[1]):
        sublst = [v for _, v in g]
        parts.append(sublst)
    return parts

def literals_from_domains(domains):

    new_literals = []
    for var, dom in domains.items():
        if len(dom) == 1:
            new_literals.append(var == next(iter(dom)))
            continue
        elif len(dom) == 0:
            # return sorted([lit for lit in literals if var in set(get_variables(lit))], key=str)
            return [cp.BoolVal(False)]

        regions = split_to_nonconsequetive(dom)
        parts = []
        for vals in regions:
            if len(vals) == 1:
                parts.append(var == vals[0])
            else:
                if min(vals) == var.lb:
                    parts.append(var <= max(vals))
                elif max(vals) == var.ub:
                    parts.append(var >= min(vals))
                else:
                    parts.append((var >= min(vals)) & (var <= max(vals)))
        if len(parts) == 1 and isinstance(parts[0], Operator) and parts[0].name == "and":
            new_literals += parts[0].args # don't make it into an "AND" constraint
        else:
            new_literals.append(cp.any(parts))

    return toplevel_list(new_literals)

def minimize_literals(literals):

    if cp.BoolVal(False) in set(literals):
        return [cp.BoolVal(False)]

    domains = get_domains_from_literals(literals)
    return literals_from_domains(domains)


def pretty_print_proof(proof, indent=0):
    proof_dict = {step['id']: step for step in proof}

    for i, step in enumerate(proof):
        lines = []
        other_steps = [i for i in step['reasons'] if isinstance(i, int)]
        cons = [c for c in step['reasons'] if isinstance(c, Expression)]
        assert len(other_steps)+len(cons) == len(step['reasons'])
        lines += ["    Reasons"]
        lines += ["        " + str(proof_dict[i]['derived']) for i in other_steps]
        lines += ["        " + str(c) for c in cons]

        if hasattr(step, "filtering_algorithm"):
            lines += [f"    Derived using {step['filtering_algorithm']}:"]
        else:
            lines += [f"    Derived:"]
        lines += ["        "+str(step['derived'])]

        width = max(len(l) for l in lines)
        print("--",i+1,"-"*(width+1-len(str(i+1))), sep="")
        for line in lines:
            print("    "*indent,"|", line," "*(width-len(line)+1),"|", sep="")
        print("-"*(width+3))

def print_explanation_step(step, index=1, indent=0, format="domain", **kwargs):
    lines = []
    if format == "literals":
        lines += ["    Input literals:"]
        lines += ["        " + ",".join(map(str, step['input_lits']))]
    elif format == "minliterals":
        lines += ["    Input literals:"]
        lines += ["        " + ",".join(map(str, minimize_literals(step['input_lits'])))]
    elif format == "domain":
        lines += ["    Input domains:"]
        domains = get_domains_from_literals(step['input_lits'])
        parts = []
        for var in get_variables(step['constraints']):
            if var in domains:
                parts.append(f"{var} ∈ {sorted(domains[var])}")
            else:
                parts.append(f"{var} ∈ [{var.lb}..{var.ub}]")
        lines += ["         " + ", ".join(parts)]
    else:
        raise ValueError(f"Expected 'literals' or 'domain' as format but got {format}")

    lines += ["    Constraints:"]
    lines += ["        " + repr(c) for c in sorted(step['constraints'], key=str)]

    lines += ["    Output literals:"]
    if format == "literals":
        lines += ["        " + ",".join(map(str, step['output_lits']))]
    elif format == "minliterals":
        lines += ["        " + ",".join(map(str, minimize_literals(step['output_lits'])))]

    width = max(len(l) for l in lines)
    print("    " * indent, "--", index, "-" * (width + 1 - len(str(index + 1))), sep="", **kwargs)
    for line in lines:
        print("    " * indent, "|", line, " " * (width - len(line) + 1), "|", sep="",  **kwargs)
    print("    " * indent+"-" * (width + 3), **kwargs)


def pretty_print_sequence(sequence, indent=0, format="literals", start_at=1, **kwargs):

    i = start_at
    for step in sequence:
        print_explanation_step(step, i, indent, format=format, **kwargs)
        i += 1





