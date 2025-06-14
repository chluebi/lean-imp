# Lean-IMP

This repository contains my current proofs surrounding the IMP pseudoprogramming language and its semantics.

# Big step vs Small Step

There are two semantics defined for IMP execution. One is Big Step (also often known as Natural Semantics) and the other is Small Step (also often known as Structural Operational Semantics). Big Step semantics builds up an entire proof tree from a program, often leading to gigantically high trees. Small Step semantics more closely follows normal sequential execution creating a sequence of proof trees.

# Proofs in this repository

The repository contains several proofs about the two languages as well as some experimental/unsafe features and programs. One core proof is the equivalence of the two semantics, meaning the translation of one execution witness into the other and back. This allows for either semantic to work as a drop-in replacement for the other.

The proofs are not nice or cleaned up and the entire repository could profit from better structure and usage of namespaces.