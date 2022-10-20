from __future__ import annotations
from typing import Iterable, List, Tuple

import argparse

from stree import Sig, LabeledModel, Prefix, QuantifierFreeFormula, QuantifiedFormula, STree
from stree import Negation, Top, Bot  # instance of QuantifierFreeFormula
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


def try_phi(strees: Iterable[STree], phi: QuantifierFreeFormula) -> Tuple[List[STree], List[STree]]:
    # print(f"Trying {phi}")
    (failures, ok) = verify(strees, phi)
    # if failures:
    #     print(failures[0])
    # else:
    #     print('No failures')
    failures_updated = update_strategies(failures, phi)
    # if failures_updated:
        # print(failures_updated[0])
    # print(f"Done trying {phi}")
    return failures_updated, ok 


def initialize_strategy_trees(ms: Iterable[LabeledModel], pre: Prefix) -> List[STree]:
    return list(map(lambda m: STree(m, pre) if m.positive else STree(m, flip(pre)), ms))


def stragus(signature: Sig, models: Iterable[LabeledModel], prefix: Prefix, options: dict = None) -> QuantifiedFormula:
    if options is None:
        options = {}

    def loop(pre: Prefix, strees: Iterable[STree], phi: QuantifierFreeFormula, counter=0):
        updated, ok = try_phi(strees, phi)
        if not updated:
            return QuantifiedFormula(pre, phi)
        else:
            strees = updated + ok
            phi = synthesize(signature, strees, options={**options, 'name': f'synth{str(counter)}'})
            return loop(pre, strees, phi, counter + 1)

    strategy_trees = initialize_strategy_trees(models, prefix)
    phi = Top()
    updated, ok = try_phi(strategy_trees, phi)
    if not updated:
        return QuantifiedFormula(prefix, phi)
    else:
        return loop(prefix, updated + ok, Bot())


if __name__ == "__main__":
    print("main running...")
