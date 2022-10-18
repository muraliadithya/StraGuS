from __future__ import annotations
from typing import Iterable, List, Tuple

import argparse

from stree import Sig, LabeledModel, Prefix, QuantifierFreeFormula, QuantifiedFormula, STree
from stree import Negation  # instance of QuantifierFreeFormula
from stree import update_strategies, flip
from synth import synthesize


def verify(strees: Iterable[STree], phi: QuantifierFreeFormula) -> Tuple[List[STree], List[STree]]:
    failures = []
    ok = []
    for stree in strees:
        if stree.model.positive:
            if not QuantifiedFormula(stree.prefix, phi).interpret_sentence(stree.model):
                failures += [stree]
            else:
                ok += [stree]
        else:
            if not QuantifiedFormula(stree.prefix, Negation(phi)).interpret_sentence(stree.model):
                failures += [stree]
            else:
                ok += [stree]
    return failures, ok


def initialize_strategies(ms: Iterable[LabeledModel], pre: Prefix) -> Iterable[STree]:
    return map(lambda m: STree(m, pre) if m.positive else STree(m, flip(pre)), ms)


def stragus(signature: Sig, models: Iterable[LabeledModel], prefix: Prefix, options: dict = None) -> QuantifiedFormula:
    if options is None:
        options = {}

    def loop(ms: Iterable[LabeledModel], pre: Prefix, strees: Iterable[STree]):
        phi = synthesize(signature, strees, options=options)
        (failures, ok) = verify(strees, phi)
        if not failures:
            return QuantifiedFormula(pre, phi)
        else:
            failures_updated = update_strategies(failures, phi)
            return loop(ms, pre, ok + failures_updated)

    strategy_trees = initialize_strategies(models, prefix)
    return loop(models, prefix, strategy_trees)


if __name__ == "__main__":
    print("main running...")
