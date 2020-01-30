# lpp-interpreter
A simple interpreter for a simple language.

## Install and run
To install the required dependencies use pip
```
$ pip install lark-parser
```
then run the interpreter on a file just do
```
$ python interpreter.py myprogram.lpp
```

## Example program
Here is an example for a program that prints the factorial of the first 20 natural numbers
```
j := 1;
while j <= 20 do
    i := 1;
    r := 1;
    while i <= j do
        r := r * i;
        i := i + 1
    endw;
    print(r);
    j := j+1
endw
```

You can run this example by
```
$ python interpreter.py examples/factorial.lpp
```

## Language definition
The grammar for the language can be found in the source code and it is really minimal
```
program: statement
    | program ";" statement

statement: "if" boolexp "then" program "else" program "fi"
    | "while" boolexp "do" program "endw"
    | "print" "(" [exp ("," exp)*] ")"
    | IDE ":=" exp

boolexp : exp "<=" exp
    | exp ">=" exp
    | exp "==" exp
    | exp "!=" exp
    | exp "<" exp
    | exp ">" exp

exp: product
    | exp "+" product
    | exp "-" product

product: atom
    | product "*" atom
    | product "/" atom

atom: NUMBER
    | "-" atom
    | IDE
    | "(" exp ")"
```
