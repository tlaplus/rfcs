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

ProofStepId == Tok({"<"} & (Numeral^+ | {"*"}) & {">"} & (Letter | Numeral)^+)

BeginStepToken == Tok({"<"} & (Numeral^+ | {"*", "+"}) & {">"} & 
                       (Letter | Numeral)^* & {"."}^* )

String == Tok({"\""} & STRING & {"\""})

PrefixOp  ==  
  Tok({ "-", "~", "\\lnot", "\\neg", "[]", "<>",
        "DOMAIN",  "ENABLED", "SUBSET", "UNCHANGED", "UNION"})

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
                     |  PrefixOp & tok("_")
                     |  tok("_") & InfixOp & tok("_")
                     |  tok("_") & PostfixOp  

   /\  G.OperatorDefinition ::=  
            (   G.NonFixLHS 
             |  PrefixOp   & Identifier 
             |  Identifier & InfixOp & Identifier 
             |  Identifier & PostfixOp )
          &  tok("==") 
          &  G.Expression

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
             (Identifier | PrefixOp | InfixOp | PostfixOp ) 
          &  tok("<-") 
          &  G.OpOrExpression 

   /\ G.OpOrExpression ::=
          PrefixOp | InfixOp | PostfixOp | G.Lambda | G.Expression

   /\ G.Lambda ::= tok("LAMBDA") & CommaList(Identifier) 
                     & tok(":") & G.Expression

   /\ G.OpName ::= 
        (Identifier | PrefixOp | InfixOp | PostfixOp | ProofStepId)
      & (  tok("!")
         & (Identifier | PrefixOp | InfixOp | PostfixOp
              | Tok({"<<", ">>", "@"} \cup Numeral^+) )
        )^*

   /\ G.OpArgs ::= tok("(") & CommaList(G.OpOrExpression) & tok(")")

   /\ G.InstOrSubexprPrefix ::=  
      (    (Nil | ProofStepId & tok("!")) 
        & ( (   Identifier & (Nil | G.OpArgs)
              | Tok({"<<", ">>", ":"} \cup Numeral^+)
              | G.OpArgs 
              | (PrefixOp | PostfixOp) & tok("(") & G.Expression & tok(")")
              | InfixOp & tok("(") & G.Expression & tok(",") 
                  & G.Expression & tok(")")
             )
            &  tok("!")
          ) ^*
      ) \ Nil

\* /\ G.InstancePrefix ::= ...

   /\ G.GeneralIdentifier ::= 
           (G.InstOrSubexprPrefix | Nil) & Identifier 
         | ProofStepId

\* /\ G.GeneralIdentifier ::= ...
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

   /\ G.UseOrHide ::=   (  (tok("USE") & (Nil | tok("ONLY")))
                         | tok("HIDE") )
                       & G.UseBody

   /\ G.UseBody  ::=  (  (Nil | CommaList(G.Expression | tok("MODULE") & Name ))
                       & (Nil | Tok({"DEF", "DEFS"}) 
                                  & CommaList(G.OpName | 
                                                tok("MODULE") & Name ))
                      ) \ Nil


   /\ G.Expression ::= 

\*          G.GeneralIdentifier

            Name & (Nil | tok("(") & CommaList(Identifier) & tok(")")) 
               & tok("::") & G.Expression

         |  G.InstOrSubexprPrefix 
               & (Tok({"<<", ">>", ":"} \cup Numeral^+) | G.OpArgs)


         |  G.GeneralIdentifier & (Nil | G.OpArgs)

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
