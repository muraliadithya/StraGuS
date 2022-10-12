from abc import abstractmethod
from typing import Tuple, Mapping, List, Union, Callable, Dict, Set, Iterable, Any
from bidict import bidict, BidirectionalMapping
import random
import itertools 

# Just make variables integers 
# Vars = Set[str]
Sig = Dict[str,int]
Prefix = List[bool]
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

# just a base class for the thing learner sends
class QuantifierFreeFormula:
    sig: Sig

    @abstractmethod
    def interpret(self, m: Model, a: Assignment) -> bool: ...

class Conjunction(QuantifierFreeFormula):
    left: QuantifierFreeFormula
    right: QuantifierFreeFormula

    def interpret(self, m: Model, a: Assignment):
        self.left.interpret(m, a) and \
        self.right.interpret(m, a)

class Disjunction(QuantifierFreeFormula):
    left: QuantifierFreeFormula
    right: QuantifierFreeFormula

    def interpret(self, m: Model, a: Assignment):
        self.left.interpret(m, a) or \
        self.right.interpret(m, a)

class Negation(QuantifierFreeFormula):
    left: QuantifierFreeFormula

    def interpret(self, m: Model, a: Assignment):
        not self.left.interpret(m, a) 
        
class Atomic(QuantifierFreeFormula):
    name: str 
    args: List[int] # variables represented as integers

    def interpret(self, m: Model, a: Assignment):
        assert(self.sig == m.sig)
        assert(self.name in self.sig)
        assert(len(self.args) == self.sig[self.name])
        return substitute(a, self.args) in m.rels[self.name]
        
def substitute(gamma: Assignment, args: List[int]):
    return [gamma[arg] for arg in args]


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

sig0 = {"P": 1}
sig1 = {"E": 2, "R": 1, "P": 3}
# vars = set(["x1","x2","x3","x4"])

# assuming we don't pass existential witnesses around
class STree:
    stree: List[List[int]] # should have length nvars

    def __init__(self, model: Model, nvars: int):
        df = model.least() # teacher starts with least element of domain
        self.stree = list(itertools.repeat([df], nvars))

    # recursively generate assignments encoded in an stree for a given quantifier prefix
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

    def __str__(self) -> str:
        return f"{{ {str(self.stree)} }}"

# returns random models with distinct ids
def getModels(sz: int, nm: int, sg: Sig) -> Iterable[Model]:
    ms = []
    for i in range(nm):
        m = randomModel(sz, sg)
        m.setId(i)
        ms.append(m)
    return ms

def initSTrees(models, vars):
    strees = bidict() 
    for model in models:
        strees[model] = STree(model, vars)
    return strees

def respond(phi: Formula, pre: Prefix, st: BidirectionalMapping) -> BidirectionalMapping:
    return st

def main():
    print("hi")

if __name__ == "__main__":
    main()