# Formal Verification of OCaml Programs with Dynamic Memory

This repository contains the complete set of **OCaml** code, **Gospel** specifications, and **CFML** proofs referenced in the paper _**"Formal Verification of OCaml Programs with Dynamic Memory"**_, developed as part of the **Curricular Development Activity (ADC) 2025**.

The materials illustrate how to apply formal methods to verify the correctness of a doubly linked list written in  OCaml, using a combination of:

- **OCaml** for implementation  
- **Gospel** for writing modular specifications  
- **CFML** (Characteristic Formulae for ML) for machine-checked proofs of functional correctness

### 📂 Project Index

- 🐫 [OCaml Code](./dblist)  
  Core OCaml implementations of the verified programs.

- 📜 [Gospel Specifications](./dblist/dblist.mli)  
  Formal modular specifications written using the [Gospel](https://github.com/ocaml-gospel/gospel) language.

- 🔒 [CFML Proofs](./cfml/examples/Dblist/Dblist_proof.v)  
  Machine-checked proofs of correctness using [CFML (Characteristic Formulae for ML)](https://github.com/charguer/cfml).
