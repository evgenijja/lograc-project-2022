
{-# OPTIONS --overlapping-instances #-}

module Peano (AtomicFormula : Set) where

{-
   Importing the deeply embedded propositional logic together with its
   natural dediction proof system, parametrised by atomic formulae type.
-}

import NaturalDeduction
open module ND = NaturalDeduction AtomicFormula

{-
The signature for Peano arithmetic consists of:
-function symbols:
    zero of arity 
    succ of arity 
    plus of arity 
    times of arity 
-there are no relation symbols
-}