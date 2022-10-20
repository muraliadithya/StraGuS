import random

from stree import *
from utils import *
from stragus import stragus


# Tests
def test_stragus_1():
    signature = {'R': 1, 'S': 2}
    domain = {1, 2}

    # first model
    R_interp = {1, 2}  # this relation is true everywhere in this model
    S_interp = {(1, 2)}
    rels = {'R': R_interp, 'S': S_interp}
    m1 = LabeledModel(domain, rels, signature, is_pos=True, name='m1')

    # second model
    R_interp = {1}
    S_interp = {(1, 1), (2, 2), (1, 2)}
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
    models = [m1, m2]
    formula = stragus(signature, models, quantifier_prefix, options={'mode': 'basic'})
    print(formula)


def test_stragus_hub_randmodels():
    signature = {'E': 2}
    model_size = 30
    num_models = 5

    from utils import _random_model
    base_models = [_random_model(model_size, signature) for _ in range(num_models)]
    not_hub = []
    for base_model in base_models:
        tuples = base_model.rels['E']
        domain = base_model.domain
        if any(all((hub, arb) in tuples for arb in domain) for hub in domain):
            continue
        not_hub.append(base_model)
    base_models = not_hub
    print(f'Num models = {str(len(base_models))}  Size = {str(model_size)}\n\n')
    neg_models = []
    pos_models = []
    for i in range(len(base_models)):
        base_model = base_models[i]
        domain = base_model.domain
        tuples = base_model.rels['E']
        neg_models.append(LabeledModel(domain, {'E': tuples}, signature, is_pos=False, name=f"n{str(i)}"))
        hub = random.choice(list(base_model.domain))
        tuples = set.union(tuples, {(hub, d) for d in domain})
        pos_models.append(LabeledModel(domain, {'E': tuples}, signature, is_pos=True, name=f"p{str(i)}"))

    quantifier_prefix = [False, True]
    models = pos_models + neg_models
    formula = stragus(signature, models, quantifier_prefix, options={'mode': 'basic'})
    print(formula)

def test_stragus_random_k_clique(k: int):
    # ∃x1 ... ∃xk. ∀yz. /\_{i < j} xi ≠ xj /\ (\/_{i} y=xi /\ \/_{j} z=xj) /\_{i,j} -> E(y,z)
    signature = {'E': 2, 'equality': 2}
    model_size = 5
    num_models = 3
    domain = {a for a in range(model_size)}
    equality = {(x,x) for x in domain}
    ksets = [set(kset) for kset in itertools.combinations(domain, k)]

    from utils import _random_model
    # equality gets added below, so I do intend not to use signature in the next line
    base_models = [_random_model(model_size, {'E': 2}) for _ in range(num_models)]
    not_k_clique = []
    for base_model in base_models:
        tuples = base_model.rels['E']
        if all((x,y) in tuples for kset in ksets for x in kset for y in kset):
            continue
        not_k_clique.append(base_model)
    base_models = not_k_clique
    print(f'Num models = {str(len(base_models))}  Size = {str(model_size)}\n\n')
    neg_models = []
    pos_models = []
    for i in range(len(base_models)):
        base_model = base_models[i]
        domain = base_model.domain
        edges = base_model.rels['E']
        neg_models.append(LabeledModel(domain, {'E': edges, 'equality': equality}, signature, is_pos=False, name=f"n{str(i)}"))
        clique = random.choice(ksets)
        augmented_edges = set.union({(x,y) for x in clique for y in clique}, edges)
        pos_models.append(LabeledModel(domain, {'E': augmented_edges, 'equality': equality}, signature, is_pos=True, name=f"p{str(i)}"))

    quantifier_prefix = [False]*k + [True]*2
    models = pos_models + neg_models
    formula = stragus(signature, models, quantifier_prefix, options={'mode': 'basic'})
    print(formula)
    
