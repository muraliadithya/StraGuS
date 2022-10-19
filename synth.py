from __future__ import annotations
from typing import List, Tuple, Iterable

import os
import subprocess
import math
import itertools

from stree import Sig, LabeledModel, Prefix, STree, Tree

from utils import parse_qf_formula


# Preamble introducing model names and such
def preamble(model_names: List[str]):
    res = f"""
(set-logic ALL)
(set-option :random-seed 1)

;; Model names as enumerated types
(declare-datatypes ((ModelId 0)) (( {' '.join(f'({name})' for name in model_names)} )) )

"""
    return res


# Function that takes a symbol in the signature and generates a definition for it
def generate_define_fun(symbol: Tuple[str, int], models: List[LabeledModel]):
    # For now a symbol is just a name and an arity: they're all relations over integers as the SMT type
    defnstr = """
(define-fun {relname} ((mid ModelId) {paramstr}) Bool
(or
{interp}
))
"""
    relname, arity = symbol
    params = [f'x{str(i)}' for i in range(arity)]
    paramstr = ' '.join(f'({p} Int)' for p in params)
    interp = ""
    model_interp = "\n(and (= mid {name})\n       {valuation})"
    for model in models:
        name = model.name
        dom = model.domain
        rel_interp = model.rels[relname]
        rel_interp = set(tuple(arg) for arg in rel_interp)
        num_interps = len(rel_interp)
        num_total_interps = math.pow(len(dom), arity)
        valuation = None
        if num_interps == 0:
            valuation = 'false'
        elif num_interps == num_total_interps:
            valuation = 'true'
        else:
            # Decide whether we will represent the true or false tuples
            sat_tuples = True
            if num_interps >= num_total_interps / 2 + 10:  # some slack so we don't recompute for no reason
                total_interps = set(itertools.product(dom, repeat=arity))
                rel_interp = total_interps - rel_interp
                # num_interps = len(rel_interp)
                sat_tuples = False
            # Small optimization for unary relations
            if arity == 1:
                valuation = ' '.join(f"(= {params[0]} {args[0]})" for args in rel_interp)
            else:
                valuation = ' '.join('(and '
                                     f'{" ".join(f"(= {params[i]} {args[i]})" for i in range(arity))}'
                                     ')' for args in rel_interp)
            # Negate valuation appropriately
            if sat_tuples:
                valuation = f'(or {valuation})'
            else:
                valuation = f'(not (or {valuation}))'
        # Construct interpretation of rel for this model
        interp = interp + model_interp.format(name=name, valuation=valuation)
    return defnstr.format(relname=relname, paramstr=paramstr, interp=interp)


def generate_grammar(signature: Sig, num_quantifiers: int, funcname):
    grammar_template = """
;; Grammar
(synth-fun {funcname} ((mid ModelId) {paramstr}) Bool
    ((Start Bool))

    (( Start Bool (
        (and Start Start)
        (or Start Start)
        (not Start)
{atomstr}
        true
        false
        ))
    )
)
"""
    params = [f'x{str(i)}' for i in range(num_quantifiers)]
    paramstr = ' '.join(f'({p} Int)' for p in params)
    atoms = []
    for symbol in signature.items():
        relname, arity = symbol
        args = itertools.product(params, repeat=arity)
        atoms.extend([f"({relname} mid {' '.join(arg)})" for arg in args])
    indent = '      '
    atomstr = '\n'.join(indent + atom for atom in atoms)
    return params, grammar_template.format(funcname=funcname, paramstr=paramstr, atomstr=atomstr)


# Setting some options
log_path = '.logs'
os.makedirs(log_path, exist_ok=True)


def synthesize_command(options):
    mode = options.get('mode', 'basic')
    if mode == 'basic':
        command = './mini-sygus/scripts/minisy {}'
    # Enumerative mode not supported for reading formulas from stdout in stream
    # elif mode == 'enum':
    #     command = 'cvc4 --lang=sygus2 --stream {}'
    else:
        raise ValueError(f'Mode {mode} for synthesis unknown.')
    return command


# helper function for stree_to_constraint
def _stree_to_constraint_aux(tree: Tree, quantifiers: Prefix, funcname: str, model_name: str, assignment: List = None):
    if assignment is None:
        assignment = []
    if not quantifiers:
        return f"({funcname} {model_name} {' '.join(str(val) for val in assignment)})"
    else:
        assert tree
        operator = 'and' if quantifiers[0] else 'or'
        operands = ' '.join(_stree_to_constraint_aux(subtree, quantifiers[1:], funcname, model_name, assignment + [root])
                            for root, subtree in tree)
        return f"({operator} {operands})"


# function to construct the constraint corresponding to a strategy tree
def stree_to_constraint(strat: STree, funcname: str):
    model = strat.model
    name = model.name
    is_pos = model.positive
    strategy_constraint = _stree_to_constraint_aux(strat.tree, strat.prefix, funcname, model.name)
    if not is_pos:
        # negate the constraint
        strategy_constraint = f'(not {strategy_constraint})'
    comment_str = f';; constraint for model {name}'
    constraint = f'{comment_str}\n(constraint {strategy_constraint})\n'
    return constraint


def generate_constraints(strees: Iterable[STree], funcname: str):
    return ''.join(stree_to_constraint(strat, funcname) for strat in strees)


def synthesize(signature: Sig, strategy_trees: Iterable[STree], options: dict = None):
    if options is None:
        options = {}

    call_name = options.get('name', None)
    synth_file = 'synth.sy' if call_name is None else f'{call_name}.sy'
    synth_file = os.path.join(log_path, synth_file)

    models = [stree.model for stree in strategy_trees]
    num_vars = set(len(stree.prefix) for stree in strategy_trees)
    if len(num_vars) != 1:
        raise ValueError("Given strategy trees specify differing number of quantified variables.")
    num_vars = num_vars.pop()

    # Construct the input file for sygus solvers
    synth_str = ''
    # Preamble
    synth_str += preamble([model.name for model in models])
    # Definitions
    synth_str += ';; Definitions\n'
    for symbol in signature.items():
        synth_str += generate_define_fun(symbol, models) + '\n'
    # Grammar
    funcname = 'formula'
    formal_params, grammar_str = generate_grammar(signature, num_vars, funcname)
    synth_str += grammar_str
    # Constraints
    synth_str += generate_constraints(strategy_trees, funcname)
    # check-synth command
    synth_str += '\n(check-synth)'
    with open(synth_file, 'w') as f:
        f.write(synth_str)

    command = synthesize_command(options)
    proc = subprocess.Popen(command.format(synth_file), stdout=subprocess.PIPE, shell=True)
    out, err = proc.communicate()
    if err:
        raise RuntimeError(f'Synthesizer returned error:\n {err}\n')
    out = out.decode('utf-8')  # convert from bytestr
    formula_str = out.split('Bool')[1].strip()[:-1].replace(' mid ', ' ')
    return parse_qf_formula(signature, formal_params, formula_str)


# Tests
def test_synthesize_1():
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

    # full tree of plays
    def generate_full_tree(height=num_quantifiers):
        if height == 0:
            return []
        return [(d, generate_full_tree(height - 1)) for d in domain]
    full_tree = generate_full_tree()

    # strategy trees
    stree1 = STree(m1, quantifier_prefix, full_tree)
    stree2 = STree(m2, quantifier_prefix, full_tree)
    strees = [stree1, stree2]
    formula = synthesize(signature, strees, options={'mode': 'basic', 'name': 'test1'})
    print(formula)
