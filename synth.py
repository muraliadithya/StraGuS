from __future__ import annotations
from typing import List, Union, Tuple

import os
import subprocess
import math
import itertools

from stree import Sig, LabeledModel, Prefix


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
(define-fun {relname} ((m ModelId) {paramstr}) Bool
(or
{interp}
))
"""
    relname, arity = symbol
    params = [f'x{str(i)}' for i in range(arity)]
    paramstr = ' '.join(f'({p} Int)' for p in params)
    interp = ""
    model_interp = "\n(and (= m {name})\n       {valuation})"
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
                num_interps = len(rel_interp)
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


def generate_grammar(signature: Sig, quantifier_prefix: List[bool], funcname):
    grammar_template = """
;; Grammar
(synth-fun {funcname} ((m ModelId) {paramstr}) Bool
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
    num_quantifiers = len(quantifier_prefix)
    params = [f'x{str(i)}' for i in range(num_quantifiers)]
    paramstr = ' '.join(f'({p} Int)' for p in params)
    atoms = []
    for symbol in signature.items():
        relname, arity = symbol
        args = itertools.product(params, repeat=arity)
        atoms.extend([f"({relname} m {' '.join(arg)})" for arg in args])
    indent = '      '
    atomstr = '\n'.join(indent + atom for atom in atoms)
    return grammar_template.format(funcname=funcname, paramstr=paramstr, atomstr=atomstr)


# Setting some options
logpath = '.logs'
os.makedirs(logpath, exist_ok=True)


def synthesize_command(mode):
    if mode == 'basic':
        command = './mini-sygus/scripts/minisy {}'
    # Enumerative mode not supported for reading formulas from stdout in stream
    # elif mode == 'enum':
    #     command = 'cvc4 --lang=sygus2 --stream {}'
    else:
        raise ValueError(f'Mode {mode} for synthesis unknown.')
    return command


# function to construct synthesis constraints using all valuations
def synthesis_constraints_total(models: List[LabeledModel], prefix: Prefix, funcname: str):
    def valuations(modelname, domain, quantifiers=None, assignment=None):
        if quantifiers is None:
            quantifiers = prefix
        if assignment is None:
            assignment = []
        if not quantifiers:
            return f"({funcname} {modelname} {' '.join(str(val) for val in assignment)})"
        else:
            return f"({'and' if quantifiers[0] else 'or'} " \
                   f"{' '.join(valuations(modelname, domain, quantifiers[1:], assignment + [elem]) for elem in domain)})"

    constraints = ''
    for model in models:
        name = model.name
        is_pos = model.positive
        model_constraint = valuations(name, model.domain)
        if not is_pos:
            # negate the constraint
            model_constraint = f'(not {model_constraint})'
        comment_str = f';; constraint for model {name}'
        constraints += f'{comment_str}\n(constraint {model_constraint})\n'
    return constraints


def generate_constraints(models: List[LabeledModel], quantifier_prefix: Prefix, funcname: str, learner: str):
    if learner == 'total':
        return synthesis_constraints_total(models, quantifier_prefix, funcname)
    else:
        raise ValueError(f'Could not identify learning algorithm {learner}.')


def synthesize(signature: Sig, models: List[LabeledModel], quantifier_prefix: Prefix, call_name: str,
               options: dict = None):
    if options is None:
        options = {}

    synth_file = f'synth{"" if call_name is None else "_" + call_name}.sy'
    synth_file = os.path.join(logpath, synth_file)

    # Construct the string to be synthesized
    synth_str = ''
    # Preamble
    synth_str += preamble([model.name for model in models])
    # Definitions
    synth_str += ';; Definitions\n'
    for symbol in signature.items():
        synth_str += generate_define_fun(symbol, models) + '\n'
    # Grammar
    funcname = 'formula'
    synth_str += generate_grammar(signature, quantifier_prefix, funcname)
    # Constraints
    synth_str += generate_constraints(models, quantifier_prefix, funcname, options.get('learner', 'total'))
    # check-synth command
    synth_str += '\n(check-synth)'
    with open(synth_file, 'w') as f:
        f.write(synth_str)

    command = synthesize_command(options.get('mode', 'basic'))
    proc = subprocess.Popen(command.format(synth_file), stdout=subprocess.PIPE, shell=True)
    out, err = proc.communicate()
    if err:
        raise RuntimeError(f'Synthesizer returned error:\n {err}\n')
    formula = out.decode('utf-8')  # convert from bytestr
    formula = formula.split('Bool')[1].strip()[:-1]
    # Pretty printing for debugging
    prefix_str = ' '.join(
        ('A' if quantifier_prefix[i] else 'E') + ' ' + f'x{str(i)}.' for i in range(len(quantifier_prefix)))
    print(prefix_str, formula)
    return quantifier_prefix, formula


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

    models = [m1, m2]
    num_quantifiers = 2
    quantifier_prefix = [True] * num_quantifiers
    synthesize(signature, models, quantifier_prefix, call_name='test1', options={'mode': 'basic', 'learner': 'total'})


# test_synthesize_1()
