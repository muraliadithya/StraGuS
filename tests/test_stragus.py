import random

from stree import *
from utils import *
from stragus import stragus
from stree import random_model


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


def test_stragus_hub_randmodels():
    signature = {'E': 2}
    model_size = 5
    num_models = 5

    base_models = [random_model(model_size, signature) for _ in range(num_models)]
    neg_models = []
    pos_models = []
    for i in range(len(base_models)):
        base_model = base_models[i]
        domain = base_model.domain
        rels = base_model.rels
        neg_models.append(LabeledModel(domain, rels, signature, is_pos=False, name=f"n{str(i)}"))
        hub = random.choice(list(base_model.domain))
        rels['E'].extend([hub, d] for d in domain)
        pos_models.append(LabeledModel(domain, rels, signature, is_pos=True, name=f"p{str(i)}"))

    quantifier_prefix = [False, True]
    models = pos_models + neg_models
    formula = stragus(signature, models, quantifier_prefix, options={'mode': 'basic'})
    print(formula)
