This is a large corpus of tests for TLA⁺ semantic validation.
Semantic validation includes resolving identifiers to specific definitions and also level-checking.
Correctness assertions are encoded *in* the TLA⁺ language itself, with calls to `RefersTo` and `IsLevel` operators defined in the [`Semantics.tla`](Semantics.tla) module.
Projects implementing these tests should search out these calls in each module and inspect the parse tree at that point to ensure the assertions are correct.
These tests make heavy use of the comment-attach feature, where comments before a definition are associated with that definition programmatically.
Currently, the following projects have adapted these tests:
1. [SANY](https://github.com/tlaplus/tlaplus/tree/master/tlatools/org.lamport.tlatools/src/tla2sany)

