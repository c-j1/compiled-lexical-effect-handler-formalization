Coq formalization of the syntax and operational semantics of LEXI and SALT, the compiler from LEXI to SALT, and the proof of correctness of compiler.

Lexi.v contains the abstract syntax and operational semantics of Lexi, the IR supporting lexical scoped effect handlers.
Salt.v contains the abstract syntax and operational semantics of Salt, the assembly language.
LexiToSalt.v defines translation/compiler from Lexi to Salt.
RelConfig.v defines predicate relating the runtime configurations of Lexi and Salt.
SimProof.v contains the simulation proof for the correctness of translation.
