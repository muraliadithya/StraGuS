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


def initialize_strategy_trees(ms: Iterable[LabeledModel], pre: Prefix) -> Iterable[STree]:
    return map(lambda m: STree(m, pre) if m.positive else STree(m, flip(pre)), ms)


def stragus(signature: Sig, models: Iterable[LabeledModel], prefix: Prefix, options: dict = None) -> QuantifiedFormula:
    if options is None:
        options = {}

    def loop(pre: Prefix, strees: Iterable[STree], phi: QuantifierFreeFormula):
        updated, ok = try_phi(strees, phi)
        if not updated:
            return QuantifiedFormula(pre, phi)
        else:
            phi = synthesize(signature, updated + ok, options=options)
            return loop(pre, strees, phi)

    def try_phi(strees: Iterable[STree], phi: QuantifierFreeFormula) -> Tuple[Iterable[STree], Iterable[STree]]:
        (failures, ok) = verify(strees, phi)
        failures_updated = update_strategies(failures, phi)
        return failures_updated, ok 

    strategy_trees = initialize_strategy_trees(models, prefix)
    phi = Top # @AD add your Top here, same for the lone Bot below
    updated, ok = try_phi(strategy_trees, phi)
    if not updated:
        return QuantifiedFormula(prefix, phi)
    else:
        return loop(prefix, updated + ok, Bot)


if __name__ == "__main__":
    print("main running...")
