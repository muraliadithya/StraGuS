import json

from utils import parse_qf_formula, loader_json_string


# Testing the quantifier-free formula parser
def test_parser_1():
    signature = {'R': 1, 'S': 2}
    params = ['y0', 'y1', 'y2']
    formula1_str = '(or false (and (not (R y0 y1)) (or (and (R y2 y0) true) (S y1 y1 y2))))'
    formula1 = parse_qf_formula(signature, params, formula1_str)
    print(formula1)


def test_jsonstr_loader_1():
    d = {'sig': {'E': 2},
         'prefix': [False, True],
         'groundtruth': [['x0', 'x1'], '(E x0 x1)'],
         'models': {'m0': {'is_pos': True,
                           'domain': [1, 2, 3],
                           'rels': {'E': [[1, 2], [2, 3], [3, 1], [2, 1], [3, 2], [1, 3], [1, 1], [2, 2], [3, 3]]}},
                    'm1': {'is_pos': False,
                           'domain': [1, 2, 3],
                           'rels': {'E': [[1, 2], [2, 3], [3, 1]]}}
                    }
         }
    d_str = json.dumps(d)
    benchmark = loader_json_string(d_str)
    print(benchmark)
