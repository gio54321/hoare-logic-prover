import sys

import z3
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
    
    def expr_to_z3_formula(self, expr):
        # basic structural induction on the formula
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
            return 0-self.expr_to_z3_formula(e1)
        elif expr.data == "number":
            return z3.IntVal(expr.children[0])
        elif expr.data == "true":
            return True
        elif expr.data == "false":
            return False
        elif expr.data == "var":
            return self.env[expr.children[0]]
    
    def find_axiom(self, command, postcond):
        # try to find an axiom of a triple, given the
        # command and the postcondition
        if command.data == "skip":
            # in case of skip the axiom is simply {p}skip{p}
            print("found axiom for skip statement:", postcond)
            return (True, postcond)
        elif command.data == "assignment":
            # in case of an assignment, the axiom
            # is {p[E/x]}x:=E{p}
            ide, exp = command.children
            axiom = z3.substitute(postcond, (self.env[ide], self.expr_to_z3_formula(exp)))
            print("found axiom for assignment statement:", axiom)
            return (True, axiom)
        elif command.data == "if":
            # in case of an if statement there is no given axiom, however
            # we can do some kind of heuristics to find a candidate.
            # it basically search for an axiom on the first statement
            # and then tries to prove thr entire if triple with that 
            # precondition. If it fails it tries to find an axiom on
            # the second statement and tries to prove the entire triple
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
        elif command.data == "composition":
            c1, c2 = command.children
            print("trying to find an axiom for a composition statement")
            (res, ax) = self.find_axiom(c2, postcond)
            if res:
                (res, ax) = self.find_axiom(c1, ax)
                if res:
                    return (True, ax)
            return (False, None)
        else:
            print("could not find axiom")
            return (False, None)

    def prove_formula(self, what_to_prove):
        # return True is the formula provided is valid
        # for this we use a well-known fact in logic
        # that is a formula f is valid iff (not)f is unsatisfiable
        # so we negate the formula and if it is unstatisfiable,
        # then it is valid
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
            # the inference rule for the skip command is really simple
            # given a triple in the form of {p}skip{q} is sufficient to
            # prove that p=>q
            formula_to_prove = z3.Implies(precond, postcond)
            print("found skip statement, trying to prove", formula_to_prove)
            res = self.prove_formula(formula_to_prove)
            return res
        elif command.data == "assignment":
            # the inference rule for the assignment command is again simple
            # given a triple in the form of {p}x:=E{q} is sufficient to
            # prove that p=>q[E/x]
            ide, exp = command.children
            formula_to_prove = z3.Implies(
                precond,
                z3.substitute(postcond, (self.env[ide], self.expr_to_z3_formula(exp)))
            )
            print("found assignment statement, trying to prove", formula_to_prove)
            res = self.prove_formula(formula_to_prove)
            return res
        elif command.data == "if":
            # the inference rule for the if command is pretty straight forward
            # to implement: given a triple in the form of {p}if E then c else s fi{q}
            # it is sufficient to prove the two triples {p and E}c{q} and {p and not E}s{q}
            guard, s1, s2 = command.children
            print("found if statement, trying to prove the first alternative")
            res_1 = self.prove_triple(z3.And(precond, self.expr_to_z3_formula(guard)), s1, postcond)
            if res_1:
                print("now trying to prove the second alternative")
                res_2 = self.prove_triple(z3.And(precond, z3.Not(self.expr_to_z3_formula(guard))), s2, postcond)
                return res_2
            else:
                return False
        elif command.data == "composition":
            # the inference rule for the composition requires a
            # special treatment. Given a triple in the form of 
            # {p}c;s{q} is sufficient to find some predicate r
            # so that {p}c{r} and {r}s{q} are both valid triples.
            # To do that we try to find an axiom for the second triple,
            # so that we have a candidate for r, then we try to prove 
            # {p}c{r}. If this triple is valid then the whole composition
            # triple is valid
            c1, c2 = command.children
            print("found composition, trying to find axiom for the right side")
            (res, axiom) = self.find_axiom(c2, postcond)
            if res:
                return self.prove_triple(precond, c1, axiom)
            else:
                return False
        elif command.data == "while":
            # the inference rule for the while command is kind of complicated
            # so we have to be careful: given a triple in the form
            # of {p}while E do C endw{q} we need a loop invariant (inv) and a counter (t)
            # we have to prove the following statements
            # 1) p => inv (pre)
            # 2) (inv and not E) => q (post)
            # 3) inv => t>=0 (termination)
            # 4) {inv and E}C{inv} (invariance)
            # 5) {inv and E and t==V}C{t<V} (progress)
            e, t_expr, inv, c = command.children
            print("found while statement, trying to prove:")
            invariant = self.expr_to_z3_formula(inv)
            t = self.expr_to_z3_formula(t_expr)
            guard = self.expr_to_z3_formula(e)
            pre = z3.Implies(precond, invariant)
            post = z3.Implies(z3.And(precond, z3.Not(guard)), postcond)
            term = z3.Implies(z3.And(invariant, self.env["t"] == t), t>=0)
            print("1) [pre]", pre)
            res = self.prove_formula(pre)
            if res:
                print("2) [post]", post)
                res = self.prove_formula(post)
                if res:
                    print("3) [term]", term)
                    res = self.prove_formula(term)
                    if res:
                        print("4) [invariance]", term)
                        res = self.prove_triple(z3.And(invariant, guard), c, invariant)
                        if res:
                            print("5) [progress]", term)
                            v = z3.Int("V")
                            res=self.prove_triple(
                                z3.And(z3.And(invariant, guard), t==v),
                                c,
                                t<v
                            )
                            return res
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
