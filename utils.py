import warnings
import time
import re
from cpmpy.expressions.core import Expression
from cpmpy.expressions.utils import flatlist

from proof2seq.mus import MUSAlgo
from proof2seq.utils import get_domains_from_literals


VAR_NAMES_REGEX = re.compile("[^0-9a-zA-Z]+")

def shrink_domains(literals: list[Expression]) -> None:
    """
    Shrink the domains of the variables, based on the literals given.
    E.g., if literals is [x >= 1, x <= 4], then the domain of x will be set to [1..4]
    Updates are done in-place.
    """
    # propagate the literals and set bounds
    smaller_domains = get_domains_from_literals(literals)
    for var, dom in smaller_domains.items():
        if len(dom) == 0:
            raise ValueError(f"literals are conflicting, this is unexpected! {literals}")
        if len(dom) != 1 + (max(dom) - min(dom)):
            warnings.warn(f"got a domain with holes, this is unexpected, propagators normally don't create holes. {literals}")
        else:
            var.lb, var.ub = min(dom), max(dom)


def lex_mus_algo(mus_algo: MUSAlgo, lex_soft: list[list[Expression]], hard: list[Expression] = [], time_limit: float = None, **kwargs):
    """
    Compute an MUS with preference of lexicographically smaller items.
    Does not guarantee to be an optimal lexicographical MUS, but works greedily.
    """
    assert isinstance(lex_soft, list)
    assert isinstance(hard, list)
    assert all(isinstance(lst, list) for lst in lex_soft)

    start = time.time()

    if len(lex_soft) == 0:
        return []

    core = []
    lex_soft = list(reversed(lex_soft))
    for i, soft in enumerate(lex_soft):

        new_piece_of_core = mus_algo.get_mus(soft=soft,
                                             hard=flatlist(hard+lex_soft[i+1:] + core),
                                             time_limit=time_limit,
                                             **kwargs)
        core += new_piece_of_core

        if time_limit is not None:
            time_limit = time_limit - (time.time() - start) # update time limit
            if time_limit <= 0:
                raise TimeoutError("Time limit exceeded while computing MUS")

    return core