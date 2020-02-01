import z3
import sys
from lark import Token

import lpp_parser

class LppProver():
    def __init__(self):
        self.lpp_parser = lpp_parser.get_lpp_parser(triple=True)
        self.env = {}

    def parse_triple(self, triple: str):
        # basically invoke the parser and return the tree
        return self.lpp_parser.parse(triple)
    
    def construnct_env(self, ides):
        if isinstance(ides, Token):
            ides = [ides]
        else:
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
        elif expr.data == "neg":
            e1 = expr.children[0]
            return -self.expr_to_z3_formula(e1)
        elif expr.data == "number":
            return z3.IntVal(expr.children[0])
        elif expr.data == "true":
            return True
        elif expr.data == "false":
            return False
        elif expr.data == "var":
            return self.env[expr.children[0]]
    
    def find_axiom(self, command, postcond):
        if command.data == "skip":
            print("found axiom for skip statement:", postcond)
            return (True, postcond)
        elif command.data == "assignment":
            ide, exp = command.children
            axiom = z3.substitute(postcond, (self.env[ide], self.expr_to_z3_formula(exp)))
            print("found axiom for assignment statement:", axiom)
            return (True, axiom)
        elif command.data == "if":
            _, s1, s2 = command.children
            print("trying to find an axiom for the first statement")
            (res, ax) = self.find_axiom(s1, postcond)
            if res:
                print("now trying to prove the entire if statement")
                res = self.prove_triple(ax, command, postcond)
                if res:
                    return (True, ax)
                else:
                    print("trying to find an axiom for the second statement")
                    (res, ax) = self.find_axiom(s2, postcond)
                    if res:
                        print("now trying to prove the entire if statement")
                        res = self.prove_triple(ax, command, postcond)
                        if res:
                            return (True, ax)
                        else:
                            print("could not find axiom for if statement")
                            return (False, None)

        else:
            print("could not find axiom")
            return (False, None)

    def prove_formula(self, what_to_prove):
        # return True is the formula provided is valid
        s = z3.Solver()
        s.add(z3.Not(what_to_prove))
        res = s.check()
        if str(res) == "unsat":
            print("proved", what_to_prove)
            return True
        else:
            print("could not prove", what_to_prove)
            return False
    
    def prove_triple(self, precond, command, postcond):
        if command.data == "skip":
            formula_to_prove = z3.Implies(precond, postcond)
            print("found skip statement, trying to prove", formula_to_prove)
            res = self.prove_formula(formula_to_prove)
            return res
        elif command.data == "assignment":
            ide, exp = command.children
            formula_to_prove = z3.Implies(
                precond,
                z3.substitute(postcond, (self.env[ide], self.expr_to_z3_formula(exp)))
            )
            print("found assignment statement, trying to prove", formula_to_prove)
            res = self.prove_formula(formula_to_prove)
            return res
        elif command.data == "composition":
            c1, c2 = command.children
            print("found composition, trying to find axiom for the right side")
            (res, axiom) = self.find_axiom(c2, postcond)
            if res:
                return self.prove_triple(precond, c1, axiom)
            else:
                return False
        elif command.data == "if":
            guard, s1, s2 = command.children
            print("found if statement, trying to prove the first alternative")
            res_1 = self.prove_triple(z3.And(precond, self.expr_to_z3_formula(guard)), s1, postcond)
            if res_1:
                print("now trying to prove the second alternative")
                res_2 = self.prove_triple(z3.And(precond, z3.Not(self.expr_to_z3_formula(guard))), s2, postcond)
                return res_2
            else:
                return False

            

    def run(self, triple):
        print("What to prove:", triple, "\n")
        tree = self.parse_triple(triple)
        self.construnct_env(tree.children[0])
        proof_res = self.prove_triple(
            self.expr_to_z3_formula(tree.children[1]),
            tree.children[2],
            self.expr_to_z3_formula(tree.children[3])
        )
        if proof_res:
            print("\nThe triple is valid")
        else:
            print("\nCould not prove the validity of the triple")
        


def main():
    # if a filename is provided via command line
    # execute it
    if(len(sys.argv) >= 2):
        with open(sys.argv[1]) as f:
            prover = LppProver()
            prover.run(f.read())

if __name__ == '__main__':
    main()