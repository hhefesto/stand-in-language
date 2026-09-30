import Base
import ./Lexical.bend as Lexical
import ./Show.bend as Show
import ./Loc.bend as Loc
import ./Text.bend as Text
import ./Syntax.bend as Syntax
import ./Lex.bend as Lex
import ./Parse.bend as Parse
import ./Expand.bend as Expand
import ./Resolve.bend as Resolve
import ./Desugar.bend as Desugar
import ./Term.bend as Term
import ./Lower.bend as Lower
import ./Split.bend as Split
import ./Front.bend as Front
import ./Main.bend as Main

# Every module of the port, so that `bend bend/Everything.bend` checks them all
# (types, termination, laws) and prints "ALL PROOFS CHECK". No main: checking
# is the whole job. Add each new module here.
