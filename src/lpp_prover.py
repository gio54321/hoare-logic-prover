import z3
import sys

import lpp_parser

class LppProver():
    def __init__(self):
        self.lpp_parser = lpp_parser.get_lpp_parser(triple=True)
        self.env = {}

    def parse_triple(self, triple: str):
        # basically invoke the parser and return the tree
        return self.lpp_parser.parse(triple)
    
    def construnct_env(self, ides):
        # convert ides to strings
        ides = list(map((lambda x: x.value), ides.children))

        # construct z3 symbols for all the ides
        env_str = ' '.join(ides)
        ide_symols = z3.Ints(env_str)

        # construct the environment
        for (i, ide) in enumerate(ides):
            self.env[ide] = ide_symols[i]
    
    # basic structural induction on the formula
    def expr_to_z3_formula(self, expr):
        if expr.data == "le":
            e1, e2 = expr.children
            return self.expr_to_z3_formula(e1) <= self.expr_to_z3_formula(e2)
        elif expr.data == "ge":
            e1, e2 = expr.children
            return self.expr_to_z3_formula(e1) >= self.expr_to_z3_formula(e2)
        elif expr.data == "eq":
            e1, e2 = expr.children
            return self.expr_to_z3_formula(e1) == self.expr_to_z3_formula(e2)
        elif expr.data == "neq":
            e1, e2 = expr.children
            return self.expr_to_z3_formula(e1) != self.expr_to_z3_formula(e2)
        elif expr.data == "lt":
            e1, e2 = expr.children
            return self.expr_to_z3_formula(e1) < self.expr_to_z3_formula(e2)
        elif expr.data == "gt":
            e1, e2 = expr.children
            return self.expr_to_z3_formula(e1) > self.expr_to_z3_formula(e2)
        elif expr.data == "and":
            e1, e2 = expr.children
            return z3.And(self.expr_to_z3_formula(e1), self.expr_to_z3_formula(e2))
        elif expr.data == "or":
            e1, e2 = expr.children
            return z3.Or(self.expr_to_z3_formula(e1), self.expr_to_z3_formula(e2))
        elif expr.data == "not":
            e1 = expr.children[0]
            return z3.Not(self.expr_to_z3_formula(e1))
        elif expr.data == "add":
            e1, e2 = expr.children
            return self.expr_to_z3_formula(e1) + self.expr_to_z3_formula(e2)
        elif expr.data == "sub":
            e1, e2 = expr.children
            return self.expr_to_z3_formula(e1) - self.expr_to_z3_formula(e2)
        elif expr.data == "mul":
            e1, e2 = expr.children
            return self.expr_to_z3_formula(e1) * self.expr_to_z3_formula(e2)
        elif expr.data == "div":
            e1, e2 = expr.children
            return self.expr_to_z3_formula(e1) / self.expr_to_z3_formula(e2)
        elif expr.data == "number":
            return z3.IntVal(expr.children[0])
        elif expr.data == "var":
            return self.env[expr.children[0]]

    def prove_formula(self, what_to_prove):
        # return True is the formula provided is valid
        s = z3.Solver()
        s.add(z3.Not(what_to_prove))
        res = s.check()
        if str(res) == "unsat":
            print("proved", what_to_prove)
            return True
        else:
            print("cound not prove", what_to_prove)
            return False
    
    def prove_triple(self, precond, command, postcond):
        if command.data == "skip":
            print("found skip command, trying to prove", z3.Implies(precond, postcond))
            res = self.prove_formula(z3.Implies(precond, postcond))
            return res

    def run(self, triple):
        tree = self.parse_triple(triple)
        self.construnct_env(tree.children[0])
        proof_res = self.prove_triple(
            self.expr_to_z3_formula(tree.children[1]),
            tree.children[2],
            self.expr_to_z3_formula(tree.children[3])
        )
        if proof_res:
            print("The triple is valid")
        else:
            print("The triple is not valid")
        


def main():
    # if a filename is provided via command line
    # execute it
    if(len(sys.argv) >= 2):
        with open(sys.argv[1]) as f:
            prover = LppProver()
            prover.run(f.read())

if __name__ == '__main__':
    main()