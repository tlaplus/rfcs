--------------------------- MODULE TLAPlus2Grammar --------------------------- 
EXTENDS Naturals, Sequences, BNFGrammars

CommaList(L) == L & (tok(",") &  L)^*
AtLeast4(s) == Tok({s \o s \o s} & {s}^+)

ReservedWord == 
  { "ASSUME",        "ELSE",       "LOCAL",       "UNION",     
    "ASSUMPTION",    "ENABLED",    "MODULE",      "VARIABLE",   
    "AXIOM",         "EXCEPT",     "OTHER",      "VARIABLES",  
    "CASE",          "EXTENDS",    "SF_",         "WF_",      
    "CHOOSE",        "IF",         "SUBSET",      "WITH", 
    "CONSTANT",      "IN",         "THEN",               
    "CONSTANTS" ,    "INSTANCE",   "THEOREM",     "COROLLARY",
    "DOMAIN",        "LET",        "UNCHANGED",   
    "BY",            "HAVE",       "QED",         "TAKE",                   
    "DEF",           "HIDE",       "RECURSIVE",   "USE", 
    "DEFINE",        "PROOF",      "WITNESS",     "PICK",
    "DEFS",          "PROVE",      "SUFFICES",    "NEW",
    "LAMBDA",        "STATE",      "ACTION",      "TEMPORAL",   
    "OBVIOUS",       "OMITTED",    "LEMMA",       "PROPOSITION",
    "ONLY"}

Letter == OneOf("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ")
Numeral   == OneOf("0123456789") 
NameChar  == Letter \cup Numeral \cup {"_"}  

Name == Tok((NameChar^* & Letter & NameChar^*)  
                   \   ({"WF_","SF_"} & NameChar^+))

Identifier == Name  \  Tok(ReservedWord)

IdentifierOrTuple  ==   
   Identifier |  tok("<<") & CommaList(Identifier) & tok(">>")

NumberLexeme == 
         Numeral^+ 
      |  (Numeral^* & {"."} & Numeral^+) 
      |  {"\\b","\\B" } & OneOf("01")^+ 
      |  {"\\o", "\\O"} & OneOf("01234567")^+ 
      |  {"\\h", "\\H"} & OneOf("0123456789abcdefABCDEF")^+ 

Number == Tok(NumberLexeme)

\* Modified by ahelwer on May 11, 2021
\* Proof step names can be any valid NameChar
ProofStepId == Tok({"<"} & (Numeral^+ | {"*"}) & {">"} & NameChar^+)

BeginStepToken == Tok({"<"} & (Numeral^+ | {"*", "+"}) & {">"} & 
                       NameChar^* & {"."}^* )

String == Tok({"\""} & STRING & {"\""})

\* Modified by ahelwer on May 26, 2021
\* Split rules to distinguish cases where -. is used instead of -
\* Any place you see StandalonePrefixOp used was modified for this purpose
PrefixOpExceptNegative ==
  { "~", "\\lnot", "\\neg", "[]", "<>",
    "DOMAIN",  "ENABLED", "SUBSET", "UNCHANGED", "UNION"}

StandalonePrefixOp ==
  Tok(PrefixOpExceptNegative \cup {"-."})

PrefixOp  ==  
  Tok(PrefixOpExceptNegative \cup {"-"})

InfixOp   ==
  Tok({  "!!",  "#",    "##",   "$",    "$$",   "%",    "%%",  
         "&",   "&&",   "(+)",  "(-)",  "(.)",  "(/)",  "(\\X)",  
         "*",   "**",   "+",    "++",   "-",    "-+->", "--",  
         "-|",  "..",   "...",  "/",    "//",   "/=",   "/\\",  
         "::=", ":=",   ":>",   "<",    "<:",   "<=>",  "=",  
         "=<",  "=>",   "=|",   ">",    ">=",   "??", 
         "@@",  "\\",   "\\/",  "^",    "^^",   "|",    "|-",  
         "|=",  "||",   "~>",   ".",    "<=",
         "\\approx",  "\\geq",       "\\oslash",     "\\sqsupseteq",
         "\\asymp",   "\\gg",        "\\otimes",     "\\star",     
         "\\bigcirc", "\\in",        "\\prec",       "\\subset",   
         "\\bullet",  "\\intersect", "\\preceq",     "\\subseteq", 
         "\\cap",     "\\land",      "\\propto",     "\\succ",     
         "\\cdot",    "\\leq",       "\\sim",        "\\succeq",   
         "\\circ",    "\\ll",        "\\simeq",      "\\supset",   
         "\\cong",    "\\lor",       "\\sqcap",      "\\supseteq", 
         "\\cup",     "\\o",         "\\sqcup",      "\\union",    
         "\\div",     "\\odot",      "\\sqsubset",   "\\uplus",    
         "\\doteq",   "\\ominus",    "\\sqsubseteq", "\\wr",      
         "\\equiv",   "\\oplus",     "\\sqsupset",   "\\notin"     })

PostfixOp ==  Tok({ "^+",  "^*", "^#", "'" })

TLAPlusGrammar ==
 LET P(G) ==
   /\ G.Module ::=     AtLeast4("-") 
                   & tok("MODULE") & Name & AtLeast4("-")
                   &   (Nil | (tok("EXTENDS") & CommaList(Name)))
                   &   (G.Unit)^* 
                   &   AtLeast4("=") 

   /\ G.Unit ::= 
              G.VariableDeclaration
           |  G.ConstantDeclaration 
           |  G.Recursive
           |  G.UseOrHide
           |  (Nil | tok("LOCAL")) & G.OperatorDefinition 
           |  (Nil | tok("LOCAL")) & G.FunctionDefinition 
           |  (Nil | tok("LOCAL")) & G.Instance           
           |  (Nil | tok("LOCAL")) & G.ModuleDefinition  
           |  G.Assumption 
           |  G.Theorem & (Nil | G.Proof)
           |  G.Module  
           |  AtLeast4("-") 

   /\ G.VariableDeclaration ::=  
          Tok({"VARIABLE", "VARIABLES"}) & CommaList(Identifier)

   /\ G.ConstantDeclaration ::=   
           Tok({"CONSTANT", "CONSTANTS"}) & CommaList(G.OpDecl)

   /\ G.Recursive ::= tok("RECURSIVE") & CommaList(G.OpDecl)

   /\ G.OpDecl ::=      Identifier 
                     |  Identifier & tok("(") & 
                               CommaList(tok("_")) & tok(")")
                     |  StandalonePrefixOp & tok("_")
                     |  tok("_") & InfixOp & tok("_")
                     |  tok("_") & PostfixOp  

   /\  G.OperatorDefinition ::=  
            (   G.NonFixLHS 
             |  StandalonePrefixOp   & Identifier 
             |  Identifier & InfixOp & Identifier 
             |  Identifier & PostfixOp )
          &  tok("==") 
          &  G.Expression

   \* Modified by ahelwer on May 25, 2021
   \* Simplified definition by removing duplicated | elements
   /\ G.NonFixLHS ::=   
             Identifier 
          &  ( Nil | tok("(") & CommaList(G.OpDecl) & tok(")") )

   /\ G.FunctionDefinition ::=   
           Identifier  
        &  tok("[") & CommaList(G.QuantifierBound) & tok("]") 
        &  tok("==") 
        &  G.Expression  

   /\ G.QuantifierBound ::=  
           (IdentifierOrTuple | CommaList(Identifier))  
        &  tok("\\in") 
        &  G.Expression 

   /\ G.Instance ::= 
           tok("INSTANCE") 
        &  Name 
        &  (Nil | tok("WITH") & CommaList(G.Substitution))  

   /\ G.Substitution ::=  
             (Identifier | StandalonePrefixOp | InfixOp | PostfixOp ) 
          &  tok("<-") 
          &  G.OpOrExpression 

   \* Modified by ahelwer on April 29, 2021
   \* Defined common OpOrExpression rule to simplify rules elsewhere
   /\ G.OpOrExpression ::=
          StandalonePrefixOp | InfixOp | PostfixOp | G.Lambda | G.Expression

   \* Modified by ahelwer on May 25, 2021
   \* Removed rule subsumed by simpler OpOrExpression rule
\* /\ G.Argument ::=...

   /\ G.Lambda ::= tok("LAMBDA") & CommaList(Identifier) 
                     & tok(":") & G.Expression

   \* Modified by ahelwer on May 25, 2021
   \* Removed rule subsumed by simpler OpOrExpression rule
\* /\ G.OpName ::=...

   /\ G.OpArgs ::= tok("(") & CommaList(G.OpOrExpression) & tok(")")

   \* Modified by ahelwer on May 25, 2021
   \* Defined common SubexprComponent and SubexprTreeNav rules
   \* Ensured rule must start with either operator or proof step ID
   \* Allowed use of @ as a parse tree navigation expression
   /\ G.InstOrSubexprPrefix ::=
           (G.SubexprComponent | ProofStepId) & tok("!")
        &  ((G.SubexprComponent | G.SubexprTreeNav) & tok("!"))^*
   
   /\ G.SubexprComponent ::=
           G.BoundOp
        |  G.BoundNonfixOp
        |  StandalonePrefixOp
        |  InfixOp
        |  PostfixOp

   /\ G.SubexprTreeNav ::=
           Tok({"<<", ">>", ":", "@"} \cup Numeral^+)
        |  G.OpArgs

   /\ G.BoundOp ::= Identifier & (Nil | G.OpArgs)

   \* Modified by ahelwer on June 17, 2021
   \* Added missing definition of nonfix operators to grammar
   /\ G.BoundNonfixOp ::=
           StandalonePrefixOp & tok("(") & G.Expression & tok(")")
        |  InfixOp & tok("(") & G.Expression & tok(",")
             & G.Expression & tok(")")
        |  PostfixOp & tok("(") & G.Expression & tok(")")

\* /\ G.InstancePrefix ::= ...

   \* Modified by ahelwer on May 26, 2021
   \* Moved ProofStepId from GeneralIdentifier to Expression rule
   \* Moved optional parameters from Expression to GeneralIdentifier rule
   \* Optional parameters became choice between BoundOp and BoundNonfixOp
   /\ G.GeneralIdentifier ::=
           (Nil | G.InstOrSubexprPrefix)
        &  (G.BoundOp | G.BoundNonfixOp)

\* /\ G.GeneralPrefixOp   ::= ...
\* /\ G.GeneralInfixOp    ::= ...
\* /\ G.GeneralPostfixOp  ::= ...

   /\ G.ModuleDefinition ::=   G.NonFixLHS 
                             & tok("==")  
                             & G.Instance  

   /\ G.Assumption ::=  
          Tok({"ASSUME", "ASSUMPTION", "AXIOM"}) 
             & (Nil | Name & tok("==")) & G.Expression

   /\ G.Theorem ::= 
          Tok({"THEOREM", "PROPOSITION", "LEMMA", "COROLLARY"}) 
             & (Nil | Name & tok("==")) & (G.Expression | G.AssumeProve)

   /\ G.AssumeProve ::=    tok("ASSUME") 
                         & CommaList(G.Expression | G.New | G.InnerAssumeProve)
                         & tok("PROVE") 
                         & G.Expression

   /\ G.InnerAssumeProve ::= (Nil | Name & tok("::")) & G.AssumeProve

   /\ G.New ::=   ((  (Nil | tok("NEW")) 
                    & (Nil | tok("CONSTANT") | tok("VARIABLE") | tok("STATE") 
                           | tok("ACTION") | tok("TEMPORAL") ) 
                   ) \ Nil)
                & ((Identifier & tok("\\in") & G.Expression) | G.OpDecl)

   /\ G.Proof ::=   G.TerminalProof 
                  | G.NonTerminalProof

   /\ G.TerminalProof ::=   (tok("PROOF") | Nil)
                          & (  tok("BY") &  (tok("ONLY") | Nil) & G.UseBody
                             | tok("OBVIOUS")
                             | tok("OMITTED")
                            )

   /\ G.NonTerminalProof ::= 
             (Nil | tok("PROOF")) 
           & G.Step^*
           & G.QEDStep

   /\ G.Step ::=
          BeginStepToken
        & (  (  G.UseOrHide
              | (  (Nil | tok("DEFINE"))
                 & (  G.OperatorDefinition 
                    | G.FunctionDefinition
                    | G.ModuleDefinition )^+
                 )
              | G.Instance
              | tok("HAVE") & G.Expression
              | tok("WITNESS") & CommaList(G.Expression)
              | tok("TAKE") & (  CommaList(G.QuantifierBound) 
                               | CommaList(Identifier) )
             )
           | (  (  (  (Nil | tok("SUFFICES"))
                    & (G.Expression | G.AssumeProve)
                   )
                 | (tok("CASE") & G.Expression)
                 | (  tok("PICK") 
                    & ( CommaList(G.QuantifierBound) | CommaList(Identifier) )
                    & tok(":")
                    & G.Expression
                   )
                )
              & (Nil | G.Proof)
             )
          )

   /\ G.QEDStep ::= 
        BeginStepToken &  tok("QED") & (Nil | G.Proof)

   \* Modified by ahelwer on Feb 12, 2023
   \* Removed optional ONLY from USE ONLY expr
   /\ G.UseOrHide ::= (tok("USE") | tok("HIDE")) & G.UseBody

   /\ G.UseBody  ::=  (  (Nil | CommaList(G.Expression | tok("MODULE") & Name ))
                       & (Nil | Tok({"DEF", "DEFS"}) 
                                  & CommaList(G.OpOrExpression | 
                                                tok("MODULE") & Name ))
                      ) \ Nil

   /\ G.Expression ::= 

            Name & (Nil | tok("(") & CommaList(Identifier) & tok(")")) 
               & tok("::") & G.Expression

         |  G.InstOrSubexprPrefix & G.SubexprTreeNav

         |  G.GeneralIdentifier

         |  ProofStepId

         |  PrefixOp & G.Expression 

         |  G.Expression & InfixOp & G.Expression 

         |  G.Expression & PostfixOp

         |  tok("(") & G.Expression & tok(")") 

         |   Tok({"\\A", "\\E"}) 
           & CommaList(G.QuantifierBound)   
           & tok(":") 
           & G.Expression 

         |    Tok({"\\A", "\\E", "\\AA", "\\EE"})
           &  CommaList(Identifier) 
           &  tok(":") 
           &  G.Expression 

        |     tok("CHOOSE") 
           &  IdentifierOrTuple 
           &  (Nil | tok("\\in") & G.Expression) 
           &  tok(":") 
           &  G.Expression 

        |     tok("{")
           & (Nil | CommaList(G.Expression))
           & tok("}") 

        |     tok("{") 
           &  IdentifierOrTuple & tok("\\in") & G.Expression 
           &  tok(":") 
           &  G.Expression 
           &  tok("}") 

        |     tok("{") 
           &  G.Expression  
           &  tok(":")  
           &  CommaList(G.QuantifierBound) 
           &  tok("}") 

        |  G.Expression & tok("[") & CommaList(G.Expression)
             & tok("]")

        |     tok("[") 
           &  CommaList(G.QuantifierBound)
           &  tok("|->")  
           &  G.Expression 
           &  tok("]") 

       |  tok("[") & G.Expression & tok("->") 
                 & G.Expression & tok("]") 

       |     tok("[") 
           & CommaList(Name & tok("|->") & G.Expression) 
           & tok("]") 

       |     tok("[") 
           & CommaList(Name & tok(":") & G.Expression)  
           & tok("]") 

       |      tok("[") 
           &  G.Expression 
           &  tok("EXCEPT") 
           &  CommaList(    tok("!")
                         & ( tok(".") & Name 
                             |  tok("[") & CommaList(G.Expression) & tok("]") )^+ 
                         &  tok("=") & G.Expression ) 
           &  tok("]") 

      |  G.Expression & tok(".") & Name

      |  tok("<<") & (CommaList(G.Expression) | Nil) & tok(">>") 

      |  G.Expression & (Tok({"\\X", "\\times"}) 
              & G.Expression)^+ 

      |  tok("[")  & G.Expression & tok("]_")  
           & G.Expression 

      | tok("<<") & G.Expression & tok(">>_") & G.Expression 

      |       Tok({"WF_", "SF_"}) 
           & G.Expression  
           & tok("(") & G.Expression & tok(")") 

      |       tok("IF")   & G.Expression 
           & tok("THEN")  & G.Expression  
           & tok("ELSE") & G.Expression 

      |  tok("CASE") 
         &  ( LET CaseArm == 
                     G.Expression & tok("->") & G.Expression
              IN  CaseArm & (tok("[]") & CaseArm)^* )

         &  (      Nil 
              |  (tok("[]") & tok("OTHER") & tok("->") & G.Expression)) 

     \* Modified by ahelwer on April 29, 2021
     \* RECURSIVE can be used inside LET-IN blocks
     |        tok("LET") 
           &  (    G.OperatorDefinition 
                |  G.FunctionDefinition 
                |  G.ModuleDefinition
                |  G.Recursive)^+
           &  tok("IN") 
           &  G.Expression

     |  (tok("/\\") & G.Expression)^+ 

     |  (tok("\\/") & G.Expression)^+ 

     |  Number 

     |  String 

     |  tok("@")

IN LeastGrammar(P)

=============================================================================
