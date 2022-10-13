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
    return map(lambda b: not b, pre)
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
        return f"{{ {str(self.id)} }}" \
             + f"{{ {', '.join(map(str, self.domain))} }}" \
             + f"{{ {str(self.rels)} }}" \
             + f"{{ {str(self.sig)} }}"
    
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


# just a base class for the thing learner sends
class QuantifierFreeFormula:
    sig: Sig

    @abstractmethod
    def interpret(self, m: Model, a: Assignment) -> bool: ...

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

    def interpret(self, m: Model) -> bool: 
        
        def interpret_aux(m: Model, pre: Prefix, partial_assignment: Assignment):
            if not pre:
                return self.matrix.interpret(m, partial_assignment)
            else:
                if pre[0]: # universal
                    return all(interpret_aux(m, pre[1:], partial_assignment + [a]) for a in m.domain)
                else: # existential 
                    return any(interpret_aux(m, pre[1:], partial_assignment + [a]) for a in m.domain)
        
        return interpret_aux(m, self.prefix, [])

class Conjunction(QuantifierFreeFormula):
    left: QuantifierFreeFormula
    right: QuantifierFreeFormula

    def __str__(self) -> str:
        return f"({self.left} ∧ {self.right})"

    def interpret(self, m: Model, a: Assignment):
        return self.left.interpret(m, a) and \
               self.right.interpret(m, a)

class Disjunction(QuantifierFreeFormula):
    left: QuantifierFreeFormula
    right: QuantifierFreeFormula

    def __str__(self) -> str:
        return f"({self.left} ∨ {self.right})"

    def interpret(self, m: Model, a: Assignment):
        return self.left.interpret(m, a) or \
               self.right.interpret(m, a)

class Negation(QuantifierFreeFormula):
    left: QuantifierFreeFormula

    def __str__(self) -> str:
        return f"¬{self.left}"

    def interpret(self, m: Model, a: Assignment):
        return not self.left.interpret(m, a) 
        
class Atomic(QuantifierFreeFormula):
    name: str 
    args: List[int] # variables represented as integers

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

sig1 = {"E": 2, "R": 1, "P": 3}

c1 = Conjunction()
l = Atomic()
l.name = "E"
l.args = [0,1]
l.sig = sig1 
r = Atomic()
r.name = "P"
r.args = [1,2,1]
r.sig = sig1
c1.left = l 
c1.right = r 
c1.sig = sig1
pre = [True,False,False]
qf = c1
f = QuantifiedFormula(pre,qf)


def randomModel(size: int, sg: Sig) -> Model:
    dom = [i for i in range(size)]
    rs = {}
    # build "full" model
    for name,arity in sg.items():
        rs[name] = list(generateAllTuples(arity, dom))
    # randomly drop tuples from each relation
    rss = rs.copy()
    for name,interp in rs.items():
        for tup in interp:
            if random.choice([True,False]):
                rss[name].remove(tup)
    return Model(dom,rs,sg)

def generateAllTuples(arity: int, d: Iterable):
    return itertools.product(d, repeat=arity)

# an STree consists of a model and its strategy tree 
Tree = List[Tuple[int, Any]]

def str_of_tree(tree: Tree, pre: Prefix) -> str:
    
    def help(tree: Tree, pre: Prefix, depth: int) -> str:
        if not pre: 
            return ""            
        s = " " * depth
        if pre[0]: 
            s += "∀\n" 
        else: 
            s += "∃\n" 
        for (i,child) in tree:
            s += " "*depth + f"|{i}\n" + help(child, pre[1:], depth+1)
        return s
    
    return help(tree, pre, 0)
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

    # recursively generate assignments encoded in an stree for a given
    # quantifier prefix. Do we want this?
    def plays(self, pre: Prefix) -> List[Assignment]:

        def playsAux(p: Prefix, i: int) -> List[Assignment]:
            if not p:
                return []
            ass = playsAux(pre[1:],i+1)
            if pre[0]: # all
                return [a.insert(0, x) for x in self.stree[i] for a in ass]
            else: # exists 
                return [a.insert(0,-1) for a in ass]
        
        return playsAux(pre, 0)

# returns random models with distinct ids
def getModels(sz: int, nm: int, sg: Sig) -> Iterable[Model]:
    ms = []
    for i in range(nm):
        m = randomModel(sz, sg)
        m.setId(i)
        ms.append(m)
    return ms

def initSTrees(models: Iterable[Model], nvars: int):
    strees = bidict() 
    for model in models:
        strees[model] = STree(model, nvars)
    return strees

# ignoring models for now and just paying attention to those represented in st
def respond(phi: QuantifierFreeFormula,
            pre: Prefix,
            st: BidirectionalMapping,
            models: Iterable[LabeledModel]) -> BidirectionalMapping:
    # randomly select a model on which pre.phi fails
    ms = []
    for labeled_model, strategy_tree in st:
        assignments = labeled_model.assignments(len(pre))
        if labeled_model.positive:
            extension = list(filter(lambda a: phi.interpret(labeled_model, a), assignments))
        else:
            extension = list(filter(lambda a: phi.interpret(labeled_model, a), assignments))
        if not extension:
            if not labeled_model.positive:
                pass

def main():
    print("main running...")

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
def update_strategy(phi: QuantifierFreeFormula, stree: STree) -> STree:
    pass

if __name__ == "__main__":
    main()