# compactness-proof-coq
# Formalization of the Compactness Theorem in Coq

This repository contains the Coq formalization of the **Compactness Theorem** for first-order logic, as presented in the paper:

> **[Formalizing the Compactness theorem in  First-Order Logic within the Coq Proof Assistant]**
> Authors: Jiaxin Xie, Xiang Ji, Wensheng Yu

## Project Overview

This work provides a rigorous mechanical verification of the Compactness Theorem. We establish the equivalence between the two standard formulations of the theorem—the logical consequence property and the satisfiability property—and prove their equivalence to the Completeness Theorem.

## File Structure

The project is organized as follows:

*   `compactness_K_System1.v`: The main formalization file containing the proof of `compactness_equiv` and the core logic of the Compactness Theorem.
*    formulas_K_System.v: Defines the foundational syntax of the first-order language, including terms, formulas, and their structural properties.
*    syntax_K_System.v: Establishes the axiomatic system, including the definitions of logical consistency, derivability, and the formal deduction rules.
*    semantic_K_System.v: Contains the semantic definitions, including model theory, satisfaction, and the properties of semantic entailment.

## Requirements

*   **Coq**: Version 8.13.2.
*   **Proof General / VSCoq**: Recommended for interactive development.

## How to Build

To compile the proofs, ensure you have the necessary Coq environment set up. You can compile the files using the following command in your terminal:

```bash
coqc compactness_K_System1.v
