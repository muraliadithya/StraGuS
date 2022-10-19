from __future__ import annotations
from typing import List

import pyparsing as pp

from stree import Sig, QuantifierFreeFormula
from stree import Top, Bot, Atomic, Conjunction, Disjunction, Negation


# Simple parser to read an smtlib expression into an stree.QuantifierFreeFormula instance
class QFFormulaParser:
    signature: Sig
    params: List[str]
    Formula: pp.ParserElement

    def __init__(self, signature: Sig, params: List[str]):
        self.signature = signature
        self.params = params

        LParen = pp.Literal('(').suppress()
        RParen = pp.Literal(')').suppress()
        AndOp = pp.Literal('and').suppress()
        OrOp = pp.Literal('or').suppress()
        NotOp = pp.Literal('not').suppress()
        TrueConst = pp.Literal('true').suppress()
        FalseConst = pp.Literal('false').suppress()

        BasicSymbol = pp.Word(pp.alphanums)

        Formula = pp.Forward()
        AtomicFormula = LParen + BasicSymbol[1, ...] + RParen
        ConjunctionFormula = LParen + AndOp + Formula[...] + RParen
        DisjunctionFormula = LParen + OrOp + Formula[...] + RParen
        NegationFormula = LParen + NotOp + Formula + RParen
        Formula <<= TrueConst ^ FalseConst ^ AtomicFormula ^ ConjunctionFormula ^ DisjunctionFormula ^ NegationFormula

        @TrueConst.set_parse_action
        def _parse_true_const(string, loc, tokens):
            return Top()

        @FalseConst.set_parse_action
        def _parse_false_const(string, loc, tokens):
            return Bot()

        @AtomicFormula.set_parse_action
        def _parse_atomic_formula(string, loc, tokens):
            rel, args = tokens[0], tokens[1:]
            args_as_indices = [self.params.index(arg) for arg in args]
            return Atomic(rel, args_as_indices, self.signature)

        @ConjunctionFormula.set_parse_action
        def _parse_conjunction_formula(string, loc, tokens):
            num_args = len(tokens)
            if num_args == 0:
                return Top()
            elif num_args == 1:
                return tokens[0]
            else:
                expr = tokens[0]
                for tok in tokens[1:]:
                    expr = Conjunction(expr, tok)
                return expr

        @DisjunctionFormula.set_parse_action
        def _parse_disjunction_formula(string, loc, tokens):
            num_args = len(tokens)
            if num_args == 0:
                return Top()
            elif num_args == 1:
                return tokens[0]
            else:
                expr = tokens[0]
                for tok in tokens[1:]:
                    expr = Disjunction(expr, tok)
                return expr

        @NegationFormula.set_parse_action
        def _parse_negation_formula(string, loc, tokens):
            return Negation(tokens[0])

        # define the formula parse element to be the one after all the actions have been defined
        self.Formula = Formula

    def parse_qf_formula(self, formula_str: str) -> QuantifierFreeFormula:
        return self.Formula.parse_string(formula_str)[0]


def parse_qf_formula(signature: Sig, params: List[str], formula_str: str) -> QuantifierFreeFormula:
    parser = QFFormulaParser(signature, params)
    return parser.parse_qf_formula(formula_str)


# some general utilities
# full tree of plays
def generate_full_tree(height, domain):
    if height == 0:
        return []
    return [(d, generate_full_tree(height - 1, domain)) for d in domain]
