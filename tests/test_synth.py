from stree import LabeledModel, STree
from stree import flip
from synth import synthesize
from utils import generate_full_tree


# Tests for the synthesis function
def test_synthesize_1():
    signature = {'R': 1, 'S': 2}
    domain = {1, 2}

    # first model
    R_interp = {(1), (2)}  # this relation is true everywhere in this model
    S_interp = {(1, 2)}
    rels = {'R': R_interp, 'S': S_interp}
    m1 = LabeledModel(domain, rels, signature, is_pos=True, name='m1')

    # second model
    R_interp = {(1)}
    S_interp = {(1, 1), (2, 2), (1, 2)}
    rels = {'R': R_interp, 'S': S_interp}
    m2 = LabeledModel(domain, rels, signature, is_pos=False, name='m2')

    num_quantifiers = 2
    quantifier_prefix = [True, False]

    full_tree = generate_full_tree(num_quantifiers, domain)

    # strategy trees
    stree1 = STree(m1, quantifier_prefix, full_tree)
    stree2 = STree(m2, quantifier_prefix, full_tree)
    strees = [stree1, stree2]
    formula = synthesize(signature, strees, options={'mode': 'basic', 'name': 'test1'})
    print(formula)


def test_synthesize_hub():
    signature = {'E': 2}
    model_size = 5
    domain = set(range(model_size))

    # first model: hub
    # every element is connected to every other element
    hub = list(domain)[0]
    E_interp = {(elem1, elem2) for elem1 in domain for elem2 in domain}
    rels = {'E': E_interp}
    m1 = LabeledModel(domain, rels, signature, is_pos=True, name='m1')

    # second model: not a hub
    # every element is not connected to its 'next' element, but is connected to everything else
    E_interp = {(elem1, elem2) for elem1 in domain for elem2 in domain if elem2 != (elem1 + 1) % model_size}
    rels = {'E': E_interp}
    m2 = LabeledModel(domain, rels, signature, is_pos=False, name='m2')

    num_quantifiers = 2
    quantifier_prefix = [False, True]

    full_tree = generate_full_tree(num_quantifiers, domain)

    # strategy trees
    stree1 = STree(m1, quantifier_prefix, full_tree)
    stree2 = STree(m2, flip(quantifier_prefix), full_tree)
    strees = [stree1, stree2]
    formula = synthesize(signature, strees, options={'mode': 'basic', 'name': 'test1'})
    print(formula)
