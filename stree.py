from __future__ import annotations
from abc import abstractmethod
# from ast import Assign
# from cProfile import label
# from re import A
from typing import Tuple, Mapping, List, Union, Callable, Dict, Set, Iterable, Any
import random
import itertools

Sig = Dict[str, int]
Prefix = List[bool]


def flip(pre: Prefix) -> Prefix:
    return list(map(lambda b: not b, pre))


# Variables are represented by integers
# [x1 -> i1, ..., xn -> in] represented as [i1,...,in]
Assignment = List[int]


class Model:
    # name distinguishes models
    name: str
    domain: Set[int]
    # interpretation of "R" is a set of tuples, set and tuple both modeled as lists
    rels: Dict[str, List[List[int]]]
    # dictionary from names to arities
    sig: Sig

    def __init__(self, domain, rels, sig, name='m0'):
        self.domain = domain
        self.rels = rels
        self.sig = sig
        self.name = name

    # return the list of all assignments for nvars variables
    def assignments(self, nvars: int) -> List[Assignment]:
        return generate_all_tuples(nvars, self.domain)

    def __str__(self) -> str:
        return f"{{name: {self.name} }}" \
               + f"{{domain: {', '.join(map(str, self.domain))} }}" \
               + f"{{relations: {str(self.rels)} }}" \
               + f"{{signature: {str(self.sig)} }}"

    # useful to pick a default play for the teacher
    def least(self) -> int:
        return min(self.domain)

    def set_name(self, name: str):
        self.name = name

    # elements of the domain are non-negative, interpretations take values from domain and
    # abide by signature arity
    def well_formed(self) -> bool:
        def well_formed_interp(name: str, interp: List[List[int]], sg: Sig, dom: Set[int]):
            return name in sg.keys() \
                   and all(len(tup) == sg[name] for tup in interp) \
                   and all(i in dom for tup in interp for i in tup)

        return all(d >= 0 for d in self.domain) and all(well_formed_interp(name, interp, self.sig, self.domain)
                                                        for name, interp in self.rels.items())


class LabeledModel(Model):
    positive: bool

    def __init__(self, dm, rs, sg, is_pos, name):
        super().__init__(dm, rs, sg, name)
        self.positive = is_pos


# simple models for testing strategy updates
def model_all_vertices_2distinct_neighbours() -> Tuple[LabeledModel, QuantifiedFormula]:
    s = {"R": 1, "E": 2, "=": 2}
    d = {1, 2, 3, 4, 5}
    equality = [[x, x] for x in d]
    r = {"=": equality, "R": [[1], [2], [3], [4]], "E": [[1, 2], [1, 3], [2, 3], [3, 4], [4, 5], [5, 1]]}
    mat = Conjunction(
        Negation(Atomic("=", [1, 2], s)),
        Conjunction(Atomic("E", [0, 1], s),
                    Atomic("E", [0, 2], s)))
    formula = QuantifiedFormula([True, False, False], mat)
    return LabeledModel(d, r, s, True, "foo"), formula


def exists_hub() -> Tuple[LabeledModel, QuantifiedFormula]:
    s = {"E": 2, "=": 2}
    d = {1, 2, 3}
    equality = [[x, x] for x in d]
    r = {"=": equality, "E": [[1, 2], [1, 3], [2, 3], [2, 1], [3, 1], [3, 2]]}
    mat = Atomic("E", [0, 1], s)
    formula = QuantifiedFormula([False, True], mat)
    return LabeledModel(d, r, s, True, "foo"), formula


def exists_forall_exists() -> Tuple[LabeledModel, QuantifiedFormula]:
    s = {"R": 3}
    d = {1, 2, 3, 4}
    # equality = [[x, x] for x in d]
    r = {"R": [[1, 2, 2], [1, 1, 1], [1, 3, 3]]}
    mat = Atomic("R", [0, 1, 2], s)
    formula = QuantifiedFormula([False, True, False], mat)
    return LabeledModel(d, r, s, True, "foo"), formula


def view_strategy_change(lm: LabeledModel, f: QuantifiedFormula) -> Tuple[STree, STree]:
    before = STree(lm, f.prefix)
    after = update_strategy(f.matrix, before)
    return before, after


class QuantifiedFormula:
    prefix: Prefix
    matrix: QuantifierFreeFormula

    def __init__(self, p: Prefix, qf: QuantifierFreeFormula):
        self.prefix = p
        self.matrix = qf

    def __str__(self) -> str:
        def str_of_prefix(pre: Prefix):
            return "".join(map(lambda x: "∀" if x else "∃", pre))

        return f"{str_of_prefix(self.prefix)}. {self.matrix}"

    def interpret_formula(self, m: Model, pre: Prefix, partial_assignment: Assignment):
        if not pre:
            return self.matrix.interpret(m, partial_assignment)
        else:
            if pre[0]:  # universal
                return all(self.interpret_formula(m, pre[1:], partial_assignment + [a]) for a in m.domain)
            else:  # existential
                return any(self.interpret_formula(m, pre[1:], partial_assignment + [a]) for a in m.domain)

    def interpret_sentence(self, m: Model) -> bool:
        return self.interpret_formula(m, self.prefix, [])

    # pretends the first quantifier of pre is absent, and returns list of domain
    # elements a that make self.matrix true with prefix pre[1:] and assignment
    # partial_assignment+[a]. The intention is that this function is called when
    # pre starts with an existential.
    def extension(self, m: Model, pre: Prefix, partial_assignment: Assignment) -> List[int]:
        return list(filter(lambda a: self.interpret_formula(m, pre[1:], partial_assignment + [a]), m.domain))


# just a base class for the thing learner sends
class QuantifierFreeFormula:
    sig: Sig

    @abstractmethod
    def interpret(self, m: Model, a: Assignment) -> bool: ...


class Conjunction(QuantifierFreeFormula):
    left: QuantifierFreeFormula
    right: QuantifierFreeFormula

    def __init__(self, left: QuantifierFreeFormula, right: QuantifierFreeFormula):
        super().__init__()
        self.left = left
        self.right = right

    def __str__(self) -> str:
        return f"({self.left} ∧ {self.right})"

    def interpret(self, m: Model, a: Assignment):
        return self.left.interpret(m, a) and self.right.interpret(m, a)


class Disjunction(QuantifierFreeFormula):
    left: QuantifierFreeFormula
    right: QuantifierFreeFormula

    def __init__(self, left: QuantifierFreeFormula, right: QuantifierFreeFormula):
        super().__init__()
        self.left = left
        self.right = right

    def __str__(self) -> str:
        return f"({self.left} ∨ {self.right})"

    def interpret(self, m: Model, a: Assignment):
        return self.left.interpret(m, a) or \
               self.right.interpret(m, a)


class Negation(QuantifierFreeFormula):
    left: QuantifierFreeFormula

    def __init__(self, left: QuantifierFreeFormula):
        super().__init__()
        self.left = left

    def __str__(self) -> str:
        return f"¬{self.left}"

    def interpret(self, m: Model, a: Assignment):
        return not self.left.interpret(m, a)


class Atomic(QuantifierFreeFormula):
    name: str
    args: List[int]  # variables represented as integers

    def __init__(self, name: str, args: List[int], s: Sig):
        super().__init__()
        self.name = name
        self.args = args
        self.sig = s

    def __str__(self) -> str:
        argument_string = ", ".join(("x" + str(arg) for arg in self.args))
        return f"{self.name}({argument_string})"

    def interpret(self, m: Model, a: Assignment):
        assert (self.sig == m.sig)
        assert (self.name in self.sig)
        assert (len(self.args) == self.sig[self.name])
        valuation = [a[arg] for arg in self.args]
        return valuation in m.rels[self.name]


class Top(QuantifierFreeFormula):
    def __init__(self):
        super().__init__()

    def __str__(self) -> str:
        return "True"

    def interpret(self, m: Model, a: Assignment) -> bool:
        return True


class Bot(QuantifierFreeFormula):
    def __init__(self):
        super().__init__()

    def __str__(self) -> str:
        return "False"

    def interpret(self, m: Model, a: Assignment) -> bool:
        return False


sig0 = {"E": 2}
sig1 = {"E": 2, "R": 1, "P": 3}

# examples of quantified formula
l1 = Atomic("E", [0, 1], sig0)
phi1 = QuantifiedFormula([True, False], l1)

l2 = Atomic("E", [0, 0], sig0)
phi2 = QuantifiedFormula([True], l2)


def random_model(size: int, sg: Sig) -> Model:
    dom = [i for i in range(size)]
    rs = {}
    # build "full" model
    for name, arity in sg.items():
        rs[name] = generate_all_tuples(arity, dom)
    # randomly drop tuples from each relation
    rss = rs.copy()
    for name, interp in rs.items():
        for tup in interp:
            if random.choice([True, False]):
                rss[name].remove(tup)
    return Model(dom, rs, sg)


def generate_all_tuples(arity: int, d: Iterable) -> List[List[int]]:
    return list(map(lambda x: list(x), itertools.product(d, repeat=arity)))


# returns random models with distinct names
def get_models(sz: int, nm: int, sg: Sig) -> Iterable[Model]:
    ms = []
    for i in range(nm):
        m = random_model(sz, sg)
        m.set_name(f'm{str(i)}')
        ms.append(m)
    return ms


# an STree consists of a model and its tree.
# The following defines the tree attribute and some utility functions for it
Tree = List[Tuple[int, Any]]


def construct_default_tree(dom: Iterable[int], pre: Prefix) -> Tree:
    if not pre:
        return []
    if pre[0]:  # universals wait for a mistake to grow a tree below
        return []
    else:  # existentials get scaffolding
        ts = []
        for a in dom:
            ts.append((a, construct_default_tree(dom, pre[1:])))
        return ts


# Prints a tree like this:
#      [a]
#     /  \
#   [b] [c]
#   /    \
# [x]   [d,e]
#
# As this:
#
# a
# |b
#  |x
# |c
#  |d
#  |e
def _str_of_tree(tree: Tree, pre: Prefix, depth: int) -> str:
    if not pre:
        return ""
    s = " " * depth
    if pre[0]:
        s += "∀\n"
    else:
        s += "∃\n"
    for (i, child) in tree:
        s += " " * depth + f"|{i}\n" + _str_of_tree(child, pre[1:], depth + 1)
    return s


class STree:
    model: LabeledModel
    prefix: Prefix
    tree: Tree

    def __init__(self, model: LabeledModel, prefix: Prefix, t: Tree = None):
        self.model = model
        self.prefix = prefix
        if t:
            self.tree = t
        else:
            self.tree = construct_default_tree(self.model.domain, prefix)

    def __str__(self) -> str:
        return _str_of_tree(self.tree, self.prefix, depth=0)

    @staticmethod
    def play_exists_already(t: Tree, n: int) -> bool:
        return any([n == x for (x, _) in t])

    @staticmethod
    def plays_at_level(t: Tree) -> List[int]:
        return [n for (n, _) in t]

    @staticmethod
    def descend(t: Tree, n: int) -> Tree:
        assert STree.play_exists_already(t, n)
        tmp = [r for (x, r) in t if x == n]
        assert (len(tmp) == 1)
        return tmp[0]

    @staticmethod
    def replace(t: Tree, n: int, r: Tree) -> Tree:
        # new_tree = []
        # for (x,c) in t:
        #     new_tree
        return [(x, r) if x == n else (x, c) for (x, c) in t]

    # Create a new subtree to beat current strategy. Example:
    # ∃x∀y∃z∀w.φ(x,y,z,w) is false in a positive model. We are finding a value
    # f(x) that satisfies ∀z∃w.¬φ(x,f(x),z,w).
    @staticmethod
    def construct_new_play(pre: Prefix, matrix: QuantifierFreeFormula, m: Model, partial: Assignment) -> Tree:
        if not pre:
            return []
        if not pre[0]:
            possible_plays = QuantifiedFormula(pre, matrix).extension(m, pre, partial)
            assert possible_plays  # if we reach this point then we already found a way to make formula false
            play = possible_plays[0]
            t = STree.construct_new_play(pre[1:], matrix, m, partial + [play])
            return [(play, t)]
        else:
            ts = []
            for a in m.domain:
                ts.append((a, STree.construct_new_play(pre[1:], matrix, m, partial + [a])))
            return ts


def update_strategies(failures: Iterable[STree], phi: QuantifierFreeFormula) -> Iterable[STree]:
    # @PK: is this what you meant?
    return list(map(lambda st: update_strategy(phi, st), failures))
    # for stree in failures:
    #     update_strategy(phi, stree)


# Precondition:
# ¬(stree.model ⊧ stree.prefix.  phi) if stree.model.positive
# ¬(stree.model ⊧ stree.prefix. ¬phi) if stree.model.negative
def update_strategy(phi: QuantifierFreeFormula, stree: STree) -> STree:
    matrix = phi if stree.model.positive else Negation(phi)
    sent = QuantifiedFormula(stree.prefix, matrix)
    # sanity check that we have a mistake on hand
    assert (not sent.interpret_sentence(stree.model))
    matrix_to_check = Negation(phi) if stree.model.positive else phi
    prefix_to_check = flip(stree.prefix)
    new_tree = walk_tree(stree, prefix_to_check, matrix_to_check)
    return STree(stree.model, stree.prefix, new_tree)


def walk_tree(st: STree, prefix: Prefix, matrix: QuantifierFreeFormula) -> Tree:
    def rec(t: Tree, partial_assignment: Assignment, pre: Prefix) -> Tree:
        if not pre:
            assert (matrix.interpret(st.model, partial_assignment))
            return [(partial_assignment[-1], [])]
        if pre[0]:  # universal teacher, existential learner
            return list(map(lambda node: (node[0], rec(node[1], partial_assignment + [node[0]], pre[1:])), t))
        else:  # existential teacher, universal learner
            possible_plays = QuantifiedFormula(pre, matrix).extension(st.model, pre, partial_assignment)
            assert possible_plays  # if we reach this point then we already found a way to make formula false
            intersection = set(possible_plays) & set(STree.plays_at_level(t))
            if intersection:  # can avoid making a new play at the current level
                play = list(intersection)[0]
                # descend along an old play and update somewhere deeper
                r = rec(STree.descend(t, play), partial_assignment + [play], pre[1:])
                return STree.replace(t, play, r)
            else:  # create a new play at current level
                play = possible_plays[0]
                r = STree.construct_new_play(pre[1:], matrix, st.model, partial_assignment + [play])
                return t + [(play, r)]
    return rec(st.tree, [], prefix)
