# Formal Verification of OCaml Programs with Dynamic Memory

This repository contains the complete set of **OCaml** code, **Gospel** specifications, and **CFML** proofs referenced in the paper _**"Formal Verification of OCaml Programs with Dynamic Memory: the Case of Doubly Linked Lists**_, developed as part of the **Curricular Development Activity (ADC) 2025**.

The materials illustrate how to apply formal methods to verify the correctness of a doubly linked list written in OCaml, using a combination of:

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

- 🧠 **Tactics Cheatsheet**  
  Reference for common CFML tactics — [Official CFML Cheatsheet](https://github.com/charguer/cfml/blob/master/CHEATSHEET.md)

### 🔧 Installation Tutorials

If you'd like to reproduce or experiment with the materials, you’ll need to install **OCaml**, **Gospel**, and **CFML**. Here are helpful resources and tutorials to get started:

- 🐫 **Install OCaml (via opam)**  
  Official guide to install OCaml and `opam` (the OCaml package manager):  
  👉 [OCaml Instalation Guide](https://ocaml.org/docs/up-and-running)

- 📜 **Install Gospel**  
  Instructions for installing the Gospel specification language and its toolchain:  
  👉 [Gospel Instalation Guide](https://ocaml-gospel.github.io/gospel/getting-started/installation)

- 🔒 **Install CFML**  
  Steps for setting up the CFML framework for verifying OCaml programs:  
  👉 [CFML Instalation Guide](https://github.com/charguer/cfml#installation)
