from stree import *
from utils import *
from stragus import stragus


# hubs
def make_hub(n: int, m: Model) -> Model:
    pass


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