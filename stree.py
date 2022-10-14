from __future__ import annotations
from abc import abstractmethod
from ast import Assign
from cProfile import label
from re import A
from typing import Tuple, Mapping, List, Union, Callable, Dict, Set, Iterable, Any
from bidict import bidict, BidirectionalMapping
import random
import itertools 

# Just make variables integers 
# Vars = Set[str]
Sig = Dict[str,int]
Prefix = List[bool]
def flip(pre: Prefix) -> Prefix:
    return list(map(lambda b: not b, pre))
# [x1 -> i1, ..., xn -> in] represented as [i1,...,in]
Assignment = List[int]
# a type for bijections (want to go between stree and its corresponding model) 
STrees = BidirectionalMapping

class Model:
    # id distinguishes models
    id: int 
    domain: Set[int]
    # interpretation of "R" is a set of tuples, set and tuple both modeled as lists
    rels: Dict[str, List[List[int]]]
    # dictionary from names to arities
    sig: Sig

    def __init__(self, dm, rs, sg, id=0):
        self.domain = dm 
        self.rels = rs
        self.sig = sg
        self.id=id

    # return the list of all assignments for nvars variables
    def assignments(self, nvars: int) -> List[Assignment]:
        return generateAllTuples(nvars, self.domain)

    def __str__(self) -> str:
        return f"{{id: {str(self.id)} }}" \
             + f"{{domain: {', '.join(map(str, self.domain))} }}" \
             + f"{{relations: {str(self.rels)} }}" \
             + f"{{signature: {str(self.sig)} }}"
    
    # useful to pick a default play for the teacher
    def least(self) -> int:
        return min(self.domain)

    def setId(self, id: int):
        self.id = id

    # all of domain is non-negative, interpretations take values from domain and
    # abide by signature arity, and id is non-negative
    def wellformed(self) -> bool:
        def wellformedInterp(name: str, interp: List[List[int]], sg: Sig, dom: Set[int]):
            return name in sg.keys() \
                and all(len(tup) == sg[name] for tup in interp) \
                and all(i in dom for tup in interp for i in tup)
        return self.id >= 0 \
            and all(d >= 0 for d in self.domain) \
            and all(wellformedInterp(name,interp,self.sig,self.domain) for name,interp in self.rels.items()) 

class LabeledModel(Model):
    positive: bool
    def __init__(self, dm, rs, sg, b, id=0):
        super().__init__(dm, rs, sg, id)
        self.positive=b

class QuantifiedFormula:
    prefix: Prefix 
    matrix: QuantifierFreeFormula

    def __init__(self, p: Prefix, qf: QuantifierFreeFormula): 
        self.prefix=p 
        self.matrix=qf

    def __str__(self) -> str:
        def str_of_prefix(pre: Prefix):
            return "".join(map(lambda x: "∀" if x else "∃", pre))
        return f"{str_of_prefix(self.prefix)}. {self.matrix}"

    def interpret_formula(self, m: Model, pre: Prefix, partial_assignment: Assignment):
        if not pre:
            return self.matrix.interpret(m, partial_assignment)
        else:
            if pre[0]: # universal
                return all(self.interpret_formula(m, pre[1:], partial_assignment + [a]) for a in m.domain)
            else: # existential 
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
        return self.left.interpret(m, a) and \
               self.right.interpret(m, a)

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
    args: List[int] # variables represented as integers

    def __init__(self, name: str, args: List[int]):
        super().__init__()    
        self.name = name 
        self.args = args

    def __str__(self) -> str:
        argument_string = ", ".join(("x"+str(arg) for arg in self.args))
        return f"{self.name}({argument_string})"
    
    def interpret(self, m: Model, a: Assignment):
        assert(self.sig == m.sig)
        assert(self.name in self.sig)
        assert(len(self.args) == self.sig[self.name])
        return substitute(a, self.args) in m.rels[self.name]
        
def substitute(gamma: Assignment, args: List[int]):
    return [gamma[arg] for arg in args]

sig0 = {"E": 2}
sig1 = {"E": 2, "R": 1, "P": 3}

# examples of quantified formula
l1 = Atomic("E", [0,1])
l1.sig = sig0
phi1 = QuantifiedFormula([True,False], l1)

l2 = Atomic("E", [0,0])
l2.sig = sig0
phi2 = QuantifiedFormula([True], l2)


def randomModel(size: int, sg: Sig) -> Model:
    dom = [i for i in range(size)]
    rs = {}
    # build "full" model
    for name,arity in sg.items():
        rs[name] = generateAllTuples(arity, dom)
    # randomly drop tuples from each relation
    rss = rs.copy()
    for name,interp in rs.items():
        for tup in interp:
            if random.choice([True,False]):
                rss[name].remove(tup)
    return Model(dom,rs,sg)

def generateAllTuples(arity: int, d: Iterable) -> List[List[int]]:
    return list(map(lambda x: list(x), itertools.product(d, repeat=arity)))

# an STree consists of a model and its strategy tree 
Tree = List[Tuple[int, Any]]

def str_of_tree(tree: Tree, pre: Prefix) -> str:
    
    def _str_of_tree(tree: Tree, pre: Prefix, depth: int) -> str:
        if not pre: 
            return ""            
        s = " " * depth
        if pre[0]: 
            s += "∀\n" 
        else: 
            s += "∃\n" 
        for (i,child) in tree:
            s += " "*depth + f"|{i}\n" + _str_of_tree(child, pre[1:], depth+1)
        return s
    
    return _str_of_tree(tree, pre, 0)
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

class STree: 
    model: LabeledModel
    prefix: Prefix
    tree: Tree

    def __str__(self) -> str:
        return str_of_tree(self.tree, self.prefix)

    def __init__(self, model: LabeledModel, prefix: Prefix):
        self.model = model
        def construct_tree(dom: Iterable[int], default: int, pre: Prefix) -> Tree:
            if not pre:
                return []
            if pre[0]: # universal
                return [(default, construct_tree(dom, default, pre[1:]))]
            else: # existential
                ts = []
                for a in dom:
                    ts.append((a, construct_tree(dom, default, pre[1:])))
                return ts
        # teacher starts with least element of domain
        self.tree = construct_tree(self.model.domain, self.model.least(), prefix)
        self.prefix = prefix

    # create a new subtree to beat current strategy
    @staticmethod
    def construct_new_play(pre: Prefix, matrix: QuantifierFreeFormula, m: Model, partial: Assignment) -> Tree:
        if not pre:
            return []
        assert(not pre[0])
        possible_plays = QuantifiedFormula(pre, matrix).extension(m, pre, partial)
        assert(possible_plays)
        play = possible_plays[0]
        t = STree.construct_new_play(pre[1:], matrix, m, partial+[play])
        return [(play, t)]
        

# returns random models with distinct ids
def getModels(sz: int, nm: int, sg: Sig) -> Iterable[Model]:
    ms = []
    for i in range(nm):
        m = randomModel(sz, sg)
        m.setId(i)
        ms.append(m)
    return ms


def stragus(ms: Iterable[Model], prefix: Prefix) -> QuantifierFreeFormula:

    def loop(ms: Iterable[Model], prefix: Prefix, strategies: BidirectionalMapping[Model, STree]):
        phi = synth(ms, strategies)
        cex = verify(ms, phi)
        if not cex:
            return QuantifiedFormula(prefix, phi)
        else:
            strategies = update(ms, strategies, phi, cex)
            return loop(ms, prefix, strategies)

    return loop(ms, prefix, initialize_strategies(ms))

def initialize_strategies(ms: Iterable[LabeledModel], pre: Prefix) -> Iterable[STree]:
    return map(lambda m: STree(m, pre) if m.positive else STree(m, flip(pre)), ms)

def synth():
    pass 
def verify():
    pass 
def update(ms: Iterable[Model], strategy):
    pass

# Precondition: 
# ¬(stree.model ⊧ stree.prefix.  phi) if stree.model.positive
# ¬(stree.model ⊧ stree.prefix. ¬phi) if stree.model.negative
def update_strategy(phi: QuantifierFreeFormula, stree: STree) -> None:
    matrix = phi if stree.model.positive else Negation(phi)
    sent = QuantifiedFormula(stree.prefix, matrix)
    # sanity check that we have a mistake on hand
    assert(not sent.interpret_sentence(stree.model))
    matrix_to_check = Negation(phi) if stree.model.positive else phi
    prefix_to_check = flip(stree.prefix)
    new_tree = walk_tree(stree, prefix_to_check, matrix_to_check)
    stree.tree = new_tree 

def walk_tree(st: STree, pre: Prefix, matrix: QuantifierFreeFormula) -> Tree:
    m = st.model 
    def rec(t: Tree, partial_assignment: Assignment, pre: Prefix) -> Tree:
        if not pre: 
            assert(matrix.interpret(m, partial_assignment))
            return [(partial_assignment[-1], [])]
        if pre[0]: # universal (existential for learner)
            return list(map(lambda node: \
              (node[0], rec(node[1], partial_assignment+[node[0]], pre[1:])), t))
        else: # existential play by teacher 
            # confusing! Maybe 'extension' should be a method of QuantifierFreeFormula
            r = STree.construct_new_play(pre, matrix, m, partial_assignment)
            return t+r
    return rec(st.tree, [], pre)
    
def main():
    print("main running...")

if __name__ == "__main__":
    main()

