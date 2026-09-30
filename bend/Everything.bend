import Base
import ./Lexical.bend as Lexical
import ./Main.bend as Main

# Every module of the port, so that `bend bend/Everything.bend` checks them all
# (types, termination, laws) and prints "ALL PROOFS CHECK". No main: checking
# is the whole job. Add each new module here.
