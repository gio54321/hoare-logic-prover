from lark import Lark, Transformer, v_args

def get_lpp_parser(triple=False):
    # grammar definition for our simple language
    triple_grammar = """
        ?triple: "{" boolexp "}" program "{" boolexp "}"
    """
    program_grammar = """
        ?program: statement
            | program ";" statement -> composition

        ?statement: "if" boolexp "then" program "else" program "fi" -> if
            | "while" boolexp "do" program "endw"                   -> while
            | "print" "(" [exp ("," exp)*] ")"                      -> print
            | "skip"                                                -> skip
            | IDE ":=" exp                                          -> assignment

        ?boolexp : "(" boolexp ")"
            | boolexp "and" boolexp    -> and
            | boolexp "or" boolexp     -> or
            | "not" boolexp            -> not
            | exp "<=" exp             -> le
            | exp ">=" exp             -> ge
            | exp "==" exp             -> eq
            | exp "!=" exp             -> neq
            | exp "<" exp              -> lt
            | exp ">" exp              -> gt

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

    lpp_grammar = triple_grammar + program_grammar if triple else program_grammar
    return Lark(lpp_grammar, start='triple' if triple else 'program', parser='lalr')