from utils import parse_qf_formula


# Testing the quantifier-free formula parser
def test_parser_1():
    signature = {'R': 1, 'S': 2}
    params = ['y0', 'y1', 'y2']
    formula1_str = '(or false (and (not (R y0 y1)) (or (and (R y2 y0) true) (S y1 y1 y2))))'
    formula1 = parse_qf_formula(signature, params, formula1_str)
    print(formula1)
