import numpy as np

import cpmpy as cp

from cpmpy.expressions.core import Expression, Operator, Comparison, BoolVal
from cpmpy.expressions.variables import _BoolVarImpl, NegBoolView, _NumVarImpl
from cpmpy.expressions.utils import is_num

from cpmpy.transformations.get_variables import get_variables as cpm_get_variables
from cpmpy.transformations.negation import push_down_negation
from cpmpy.transformations.normalize import toplevel_list

from itertools import groupby


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
            else:
                newlst.append(cpm_expr)
        else:
            raise ValueError(f"Unexpected expression: {cpm_expr}")

    return sorted(newlst, key=str)


def sanity_check_nogoods(nogoods, constraints=None):
    """
    Sanity-check a list of nogood expressions.
    Each nogood must be a CPMpy Expression, and together with the model
    constraints they should be unsatisfiable.
    """
    for i, ng in enumerate(nogoods):
        if not isinstance(ng, Expression):
            raise ValueError(f"Expected Expression at index {i}, got {type(ng)}: {ng}")

    if constraints is not None and len(nogoods) > 0:
        if cp.Model(list(constraints) + list(nogoods)).solve() is not False:
            raise ValueError("constraints + nogoods are satisfiable; expected an UNSAT proof")


def sanity_check_sequence(seq):
    current_lits = []
    for step in seq:
        assert set(step['input_lits']) <= frozenset(current_lits)
        assert cp.Model(step['input_lits'] + step['constraints'] + [~cp.all(step['output_lits'])]).solve() is False
        current_lits = list(set(current_lits) | set(step['output_lits']))


def get_proof_statistics(proof):
    if len(proof) == 0:
        return dict(length=0, avg_vars=0, std_vars=0, max_vars=0)

    n_vars = [len(get_variables(ng)) for ng in proof]
    return dict(
        length=len(proof),
        avg_vars=sum(n_vars) / len(n_vars),
        std_vars=np.std(n_vars),
        max_vars=max(n_vars),
    )


def print_proof_statistics(proof, name="Proof", precision=2):
    print(f"Statistics for {name}:")
    stats = get_proof_statistics(proof)
    print("#steps:", stats['length'], end="\t")
    print("avg #vars:", round(stats['avg_vars'], precision), end="\t")
    print("std #vars:", round(stats['std_vars'], precision), end="\t")
    print("max #vars:", stats['max_vars'], end="\t")
    print("\n")


def get_sequence_statistics(sequence):
    n_cons = [len(step['constraints']) for step in sequence]
    return dict(
        length=len(sequence),
        avg_cons=sum(n_cons) / len(sequence),
        std_cons=np.std(n_cons),
        max_cons=max(n_cons),
    )


def print_sequence_statistics(sequence, precision=2):
    print("Statistics for explanation sequence:")
    stats = get_sequence_statistics(sequence)
    print("#steps:", stats['length'], end="\t")
    print("avg #constraints:", round(stats['avg_cons'], precision), end="\t")
    print("std #constraints:", round(stats['std_cons'], precision), end="\t")
    print("max #constraints:", stats['max_cons'], end="\t")
    print("\n")


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
            new_literals += parts[0].args
        else:
            new_literals.append(cp.any(parts))

    return toplevel_list(new_literals)


def minimize_literals(literals):
    if cp.BoolVal(False) in set(literals):
        return [cp.BoolVal(False)]

    domains = get_domains_from_literals(literals)
    return literals_from_domains(domains)


def step_label(prefix="", index=1):
    return f"{prefix}.{index}" if prefix else str(index)


def format_step_label(label):
    return f"Step {label}"


def pretty_print_proof(proof, indent=0):
    for i, ng in enumerate(proof):
        label = format_step_label(i + 1)
        line = f"    {ng}"
        width = max(len(line), len(label) + 1)
        print("    " * indent, label, "-" * (width - len(label)), sep="")
        print("    " * indent, "|", line, " " * (width - len(line) + 1), "|", sep="")
        print("    " * indent + "-" * (width + 3))


def print_explanation_step(step, label="1", indent=0, format="domain", **kwargs):
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

    step_tag = format_step_label(label)
    width = max(len(l) for l in lines)
    width = max(width, len(step_tag) + 1)
    print("    " * indent, step_tag, "-" * (width - len(step_tag)), sep="", **kwargs)
    for line in lines:
        print("    " * indent, "|", line, " " * (width - len(line) + 1), "|", sep="", **kwargs)
    print("    " * indent + "-" * (width + 3), **kwargs)


def pretty_print_sequence(sequence, indent=0, format="literals", prefix="", start_at=1, **kwargs):
    for i, step in enumerate(sequence, start=start_at):
        label = step_label(prefix, i)
        print_explanation_step(step, label, indent, format=format, **kwargs)
        nested = step.get("nested_explanation")
        if nested:
            pretty_print_sequence(nested, indent=indent + 1, format=format, prefix=label, **kwargs)
