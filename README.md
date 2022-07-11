# Skeleton repository for the Logika v računalništvu student projects

This repository is set up as an Agda library and it contains:

* `lograc-project.agda-lib`: the library configuration file which contains
  the list of file system paths that Agda should include

* `agda-stdlib/`: Agda standard library as a git submodule

* `agda-categories/`: Agda categories library as a git submodule

* `project/`: the top-level source code directory for your Agda code

  * `NaturalDeduction.agda` contains the foundations needed for Predicate Logic and the formalizations of Peano axioms

  * `Semantics.agda` contains the semantics as well as partially proven

# **Predicate logic** over natural numbers - goals for the project

 - extending the propositional logic from the class with (i) natural
  number typed terms, (ii) quantifiers over natural number typed
  variables, (iii) an equality predicate between natural number
  typed terms
  
  - `t ::= x | zero | suc t | t + t | t * t `
  
  - `phi, psi ::= ... | forall x . phi | exists x . phi | t = t' `

- giving the resulting logic a semantics
  
  - compared to propositional logic, here you have to consider 
    formulae in context `Gamma |- phi` where `Gamma` is a list
    of natural-number typed variables
    
  - the interpretation of formulae is then given as 
    `[[phi]] : [[Gamma]] -> HProp`


  - you also need to define well-typed terms `Gamma |- t` and 
    define for them an interpretation `[[t]] : [[Gamma]] -> ℕ`
    
  - as the contexts `Gamma` contain variables of only one type,
    they can be represented simply as a natural number `n` (the 
    length of the context), with the variables in terms then 
    being elements of `Fin n` (i.e., De Bruijn indices)

- validating in Agda that the semantics models Peano axioms

  - this means that if `Gamma |- phi` is a Peano axiom, you need 
    to show that for all `g : Gamma`, `proof ([[phi]] g)` is inhabited

- adapting the natural deduction proof system to account for the
  quantifiers and the equality predicate
  
  - in order to write down the rules for quantifiers and equality, 
    you will also need to define the operations of substituting a
    free variable in a term or formula with another term
  
  - differently from lectures, where structural properties (of
    weakening, contraction, and exchange) were included as rules 
    in their own right, in this project you will define a natural
    deduction proof system in which they are admissible
  
- giving proofs in the natural deduction system of Peano axioms



- a good starting point is the lecture notes on predicate logic
  and the propositions-as-types correspondence, together with
  Chapter 2 of "Logic in Computer Science" by Huth & Ryan

# Comments

* The main difference from our project and the original project goals is the fact that we ended up following the concept of propositions as types and evaluated the formulas in Sets instead of Hprop

* We failed to finish the proof of soundness for all axioms and introduction and elimination rules for quantifiers. Some of the proofs left would require additional lemmas or auxiliary functions.


## Sources and literature

* the foundation for this project were the class exercises on Propositional logic

* we also covered Predicate logic in class: http://www.andrej.com/zapiski/ISRM-LOGRAC-2022/05-logic.lagda.html 

* Huth & Ryan - Logic in Computer Science, Chapter 2

* https://plfa.github.io/ 

* https://agda.github.io/agda-stdlib/ 

