# Hoare logic prover
A very basic prover for Hoare triples.

## What is Hoare logic?
According to [Wikipedia](https://en.wikipedia.org/wiki/Hoare_logic), Hoare logic is a formal system with a set of logical rules for reasoning rigorously about the correctness of computer programs. It was proposed in 1969 by the British computer scientist and logician _Tony Hoare_, and subsequently refined by Hoare and other researchers. The original ideas were seeded by the work of Robert W. Floyd, who had published a similar system for flowcharts.

## What this program is
A very simple automatic prover for Hoare triplets that takes in input a triplet and tries to formally prove it using the inference rules. Because of its simplicity it is not very capable right now, and it can only prove very basic triples.

## Install and run
To install the required dependencies use pip
```
$ pip install lark-parser z3-solver
```
then to run the prover on a file just do
```
$ python src/lpp_prover.py mytriple.lpp
```

## Example triple
Here is an example triple that can give you the feeling of this system
```
[x, A]
{x==A}
x := x-3;
if (x >= 0) then
    x := x + 5
else
    x := -x + 5
fi
{x>A}
```
You can run this example by
```
$ python src/lpp_prover.py examples/if_triple.lpp
```
The output shoud look like this:
```
What to prove: [x, A]
{x==A}
x := x-3;
if (x >= 0) then
    x := x + 5
else
    x := -x + 5
fi
{x>A} 

found composition, trying to find axiom for the right side
trying to find an axiom for the first statement
found axiom for assignment statement: x + 5 > A
now trying to prove the entire if statement
found if statement, trying to prove the first alternative
found assignment statement, trying to prove Implies(And(x + 5 > A, 0 <= x), x + 5 > A)
proved Implies(And(x + 5 > A, 0 <= x), x + 5 > A)
now trying to prove the second alternative
found assignment statement, trying to prove Implies(And(x + 5 > A, Not(0 <= x)), 0 - x + 5 > A)
proved Implies(And(x + 5 > A, Not(0 <= x)), 0 - x + 5 > A)
found assignment statement, trying to prove Implies(x == A, x - 3 + 5 > A)
proved Implies(x == A, x - 3 + 5 > A)

The triple is valid
```
The verdict is that this simple triple is indeed valid (I mean, yeah obviously). One interesting thing to notice is that the proof is completely parametric as in this case `x` is parametrized with the symbol `A`.

## How dows it work?
This software heavily uses [z3](https://github.com/Z3Prover/z3) theorem prover to prove the implications. It basically do an induction on the structure of the program to find the appropriate inference rule, and tries to prove the required formulas. It also uses some heuristic guessing to find composition intermediate condition and if statement axioms, but basically it is direct application of inference rules.