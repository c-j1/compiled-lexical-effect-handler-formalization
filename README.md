# Lexa - A Programming Language Supporting Compiled Lexical Scoped Effect Handlers

This project contains the Coq formalization of the syntax and operational semantics of LEXA and SALT, the compiler from LEXA to SALT, and the proof of correctness of compiler.

## Overview of Files

- Lexa.v contains the abstract syntax and operational semantics of Lexa, the high level language supporting lexical scoped effect handlers.

- Salt.v contains the abstract syntax and operational semantics of Salt, an assembly language that Lexa compiles to.

- LexaToSalt.v defines a translation function that takes in Lexa code and produces Salt code. It is essentially a compiler, except that its input is already Lexa abstract syntax and not strings.

- RelConfig.v defines a predicate relating the runtime configurations of Lexa and Salt, which will be used in SimProof.v for the simulation proof of the compiler's correctness.

- Infrastructure.v contains some lemmas used in the proofs in SimProof.v, and some simple tactics.

SimProof.v contains the simulation proof for the correctness of translation.
