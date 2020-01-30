from lark import Lark, Transformer, v_args

def get_lpp_parser():
    # grammar definition for our simple language
    lpp_grammar = """
        ?program: statement
            | program ";" statement -> composition

        ?statement: "if" boolexp "then" program "else" program "fi" -> if
            | "while" boolexp "do" program "endw"                   -> while
            | "print" "(" [exp ("," exp)*] ")"                      -> print
            | "skip"                                                -> skip
            | IDE ":=" exp                                          -> assignment

        ?boolexp : exp "<=" exp     -> le
            | exp ">=" exp          -> ge
            | exp "==" exp          -> eq
            | exp "!=" exp          -> neq
            | exp "<" exp           -> lt
            | exp ">" exp           -> gt

        ?exp: product
            | exp "+" product       -> add
            | exp "-" product       -> sub

        ?product: atom
            | product "*" atom      -> mul
            | product "/" atom      -> div

        ?atom: NUMBER               -> number
            | "-" atom              -> neg
            | IDE                   -> var
            | "(" exp ")"
        
        %import common.CNAME -> IDE
        %import common.NUMBER
        %import common.WS
        %ignore WS
    """
    return Lark(lpp_grammar, start='program', parser='lalr')