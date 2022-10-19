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
    print(f"Trying {phi}")
    (failures, ok) = verify(strees, phi)
    if failures:
        print(failures[0])
    else:
        print('No failures')
    failures_updated = update_strategies(failures, phi)
    if failures_updated:
        print(failures_updated[0])
    print(f"Done trying {phi}")
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
            phi = synthesize(signature, updated + ok, options={**options, 'name': f'synth{str(counter)}'})
            return loop(pre, strees, phi)

    strategy_trees = initialize_strategy_trees(models, prefix)
    phi = Top()
    updated, ok = try_phi(strategy_trees, phi)
    if not updated:
        return QuantifiedFormula(prefix, phi)
    else:
        return loop(prefix, updated + ok, Bot())


if __name__ == "__main__":
    print("main running...")


# Tests
def test_stragus_1():
    signature = {'R': 1, 'S': 2}
    domain = {1, 2}

    # first model
    R_interp = [[1], [2]]  # this relation is true everywhere in this model
    S_interp = [[1, 2]]
    rels = {'R': R_interp, 'S': S_interp}
    m1 = LabeledModel(domain, rels, signature, is_pos=True, name='m1')

    # second model
    R_interp = [[1]]
    S_interp = [[1, 1], [2, 2], [1, 2]]
    rels = {'R': R_interp, 'S': S_interp}
    m2 = LabeledModel(domain, rels, signature, is_pos=False, name='m2')

    num_quantifiers = 2
    quantifier_prefix = [True, False]
    models = [m1, m2]
    formula = stragus(signature, models, quantifier_prefix, options={'mode': 'basic'})
    print(formula)


def test_stragus_hub():
    signature = {'E': 2}
    model_size = 5
    domain = set(range(model_size))

    # first model: hub
    # every element is connected to every other element
    hub = list(domain)[0]
    E_interp = [[elem1, elem2] for elem1 in domain for elem2 in domain]
    rels = {'E': E_interp}
    m1 = LabeledModel(domain, rels, signature, is_pos=True, name='m1')

    # second model: not a hub
    # every element is not connected to its 'next' element, but is connected to everything else
    E_interp = [[elem1, elem2] for elem1 in domain for elem2 in domain if elem2 != (elem1 + 1) % model_size]
    rels = {'E': E_interp}
    m2 = LabeledModel(domain, rels, signature, is_pos=False, name='m2')

    num_quantifiers = 2
    quantifier_prefix = [False, True]
    models = [m1, m2]
    formula = stragus(signature, models, quantifier_prefix, options={'mode': 'basic'})
    print(formula)
