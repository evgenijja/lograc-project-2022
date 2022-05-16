
{-
   Allowing overlapping instances for `∈` to use in `hyp`.

   Warning: If used carelessly, could lead to exponential
   slowdown and looping behaviour during instance search.
-}

{-# OPTIONS --overlapping-instances #-}


{-
   Notice that we parametrise the deeply embedded propositional logic
   and its natural deduction proof system over a type of atomic formulaes.
-}

module NaturalDeduction (AtomicFormula : Set) where

open import Data.List  using (List; []; _∷_; [_]; _++_) public
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Fin using (Fin)

{-From lectures: 

The language of a first-order theory is described by a signature, which consists of:
- a list of function symbols fᵢ each of which has an arity nᵢ ∈ ℕ,
- a list of relation symbols Rᵢ each of which has an arity kⱼ ∈ ℕ.
-}

{-
   Basis for formulae taken from lectures and exercises on propositional logic.
-}

-- expressions and formulaes have to be in context of n variables
data Exp (n : ℕ) : Set where
   --  `_ : Fin n → Exp n -- expression with n variables
    var_ : Fin n → Exp n
    zero : Exp n -- expression with n variables (not necessarily all of them)
    -- x + y is an expression in x, y, z 
    suc : Exp n → Exp n
    _+_ : Exp n → Exp n → Exp n
    _*_ : Exp n → Exp n → Exp n


data Formula (n : ℕ) : Set where
--   `_  : AtomicFormula → Formula n          -- atomic formula
  ⊤   : Formula n                          -- truth (unicode \top)
  ⊥   : Formula n                          -- falsehood (unicode \bot)
  _∧_ : Formula n → Formula n → Formula n       -- conjunction (unicode \wedge)
  _∨_ : Formula n → Formula n → Formula n       -- disjunction (unicode \vee)
  _⇒_ : Formula n → Formula n → Formula n       -- implication (unicode \=>)
  ∀∀_ : Formula (suc n) → Formula n                 -- for all \forall\forall
  ∃_ : Formula (suc n) → Formula n                   -- exists \exists
--   _≡≡_ : Exp n → Exp n → Formula n

infixr 6 _∧_
infixr 5 _∨_
infixr 4 _⇒_

infix 7 ∀∀_ -- TODO popravi vrstni red
infix 8 ∃_


{-
   Hypotheses are represented as a list of formulae.
-}

-- hypotheses also need context of n variables
Hypotheses : ℕ → Set
Hypotheses n = List (Formula n)


{-
   We use constructor instances when defining the formula-in-hypotheses
   membership relation `∈`. This way we will be able to use instance
   search to fill in these arguments when constructing derivations.

   Note: Agda will report an error if instance search is used to try to
   provide a witness of `{{x ∈ xs}}` when `xs` contains multiple copies
   of `x`, because in that case there isn't a unique proof of `x ∈ xs`.
   In those cases you can provide an explicit proof of the form `{{p}}`.

   You shouldn't be running into such errors in this week's exercises
   as their most concise solutions will involve repeated hypotheses.
-}

infix 3 _∈_
data _∈_ {A : Set} : A → List A → Set where
  instance
    ∈-here  : {x : A} → {xs : List A} → x ∈ (x ∷ xs)
    ∈-there : {x y : A} {xs : List A} → {{x ∈ xs}} → x ∈ (y ∷ xs)



infixl 2 _,_⊢_
data _,_⊢_ : (n : ℕ) → (Δ : Hypotheses n) → (φ : Formula n) → Set where    -- unicode \vdash


  -- structural rules

  weaken  : (n : ℕ) → {Δ₁ Δ₂ : Hypotheses n}
           → (φ : Formula n)
           → {ψ : Formula n}
           → n , Δ₁ ++ Δ₂ ⊢ ψ
           ---------------------------
           → n , Δ₁ ++ [ φ ] ++ Δ₂ ⊢ ψ

  contract : (n : ℕ) → {Δ₁ Δ₂ : Hypotheses n}
           → (φ : Formula n)
           → {ψ : Formula n}
           → n , Δ₁ ++ [ φ ] ++ [ φ ] ++ Δ₂ ⊢ ψ
           --------------------------------
           → n , Δ₁ ++ [ φ ] ++ Δ₂ ⊢ ψ

  exchange : (n : ℕ) → {Δ₁ Δ₂ : Hypotheses n}
           → (φ₁ φ₂ : Formula n)
           → {ψ : Formula n}
           → n , Δ₁ ++ [ φ₁ ] ++ [ φ₂ ] ++ Δ₂ ⊢ ψ
           -----------------------------------------
           → n , Δ₁ ++ [ φ₂ ] ++ [ φ₁ ] ++ Δ₂ ⊢ ψ

  -- hypotheses

  hyp      : (n : ℕ) → {Δ : Hypotheses n}
           → (φ : Formula n)
           → {{φ ∈ Δ}}
           -----------------
           → n , Δ ⊢ φ

  -- truth

  ⊤-intro  : (n : ℕ) → {Δ : Hypotheses n}
           ------------------
           → n , Δ ⊢ ⊤

  -- falsehood

  ⊥-elim   : (n : ℕ) → {Δ : Hypotheses n}
           → {φ : Formula n}
           → n , Δ ⊢ ⊥
           -------------------
           → n , Δ ⊢ φ

  -- conjunction

  ∧-intro  : (n : ℕ) → {Δ : Hypotheses n}
           → {φ ψ : Formula n}
           → n , Δ ⊢ φ
           → n , Δ ⊢ ψ
           -------------------
           → n , Δ ⊢ φ ∧ ψ
          
  ∧-elim₁  : (n : ℕ) → {Δ : Hypotheses n}
           → {φ ψ : Formula n}
           → n , Δ ⊢ φ ∧ ψ
           -------------------
           → n , Δ ⊢ φ

  ∧-elim₂  : (n : ℕ) → {Δ : Hypotheses n}
           → {φ ψ : Formula n}
           → n , Δ ⊢ φ ∧ ψ
           -------------------
           → n , Δ ⊢ ψ

  -- disjunction

  ∨-intro₁ : (n : ℕ) → {Δ : Hypotheses n}
           → {φ ψ : Formula n}
           → n , Δ ⊢ φ
           ------------------
           → n , Δ ⊢ φ ∨ ψ

  ∨-intro₂ : (n : ℕ) → {Δ : Hypotheses n}
           → {φ ψ : Formula n}
           → n , Δ ⊢ ψ
           -------------------
           → n , Δ ⊢ φ ∨ ψ

  ∨-elim   : (n : ℕ) → {Δ : Hypotheses n}
           → {φ₁ φ₂ ψ : Formula n}
           → n , Δ ⊢ φ₁ ∨ φ₂
           → n , Δ ++ [ φ₁ ] ⊢ ψ
           → n , Δ ++ [ φ₂ ] ⊢ ψ
           ---------------------
           → n , Δ ⊢ ψ

  -- implication

  ⇒-intro  : (n : ℕ) → {Δ : Hypotheses n}
           → {φ ψ : Formula n}
           → n , Δ ++ [ φ ] ⊢ ψ
           --------------------
           → n , Δ ⊢ φ ⇒ ψ

  ⇒-elim   : (n : ℕ) → {Δ : Hypotheses n}
           → {φ ψ : Formula n}
           → n , Δ ⊢ φ ⇒ ψ
           → n , Δ ⊢ φ
           -------------------
           → n , Δ ⊢ ψ

-- data Exp (n : ℕ) : Set where
--     var_ : Fin n → Exp n
--     zero : Exp n -- expression with n variables (not necessarily all of them)
--     suc : Exp n → Exp n
--     _+_ : Exp n → Exp n → Exp n
--     _*_ : Exp n → Exp n → Exp n

-- From instructions: 
-- in order to write down the rules for quantifiers and equality, you will also need to define the operations of substituting 
-- a free variable in a term or formula with another term



Sub : ℕ → ℕ → Set 
-- Sub n m = (i ∈ Fin n) → Exp m
Sub n m = Fin n → Exp m 

substₑ : ℕ → ℕ → Set 
substₑ n m = Sub m n  →  Exp n → Exp m

subst : ℕ → ℕ → Set 
subst n m = Sub m n  → Formula n → Formula m



-- Γ , Δ ⊢ t : A      Γ , Δ ⊢ u : ϕ(t)
-- ---------------------------------
-- Γ , Δ ⊢ ∃ x : A . ϕ(x)


-- ∃-intro : (n : ℕ) → {Δ : Hypotheses suc n}
--           → {ψ : Formula n} 
--           → {ϕ : Δ → ψ}
--           → (suc n) , Δ ⊢ ψ --term (expression)
--           → (suc n) , Δ ⊢ ϕ(ψ)
--        ---------------------------
--             n , Δ ⊢ ∃  




--   ∃-elim


--   ∀∀-intro   : (n : ℕ) → {Δ : Hypotheses (suc n)}
--             → {ψ : Formula (suc n)} 
--             -- ­→ {φ : Formula n}
--             → {`x : Exp n}
--             → suc n , Δ ⊢ ψ  -- from hypotheses in n+1 variables we derive ψ
--             ------------
--             → n , Δ ⊢ (∀∀ `x , Formula n)

--   ∀∀-elim    : (n : ℕ) → {Δ : Hypotheses (suc n)}
--                → {φ : Formula n}
--                → {λ : Δ → φ}
--                → n , ∀∀ λ (Δ) ⊢ φ
--                ---------------------------
--                → n , Δ ⊢ λ _

-- things are equal when they have equal parts
--   ≡≡-intro

--   ≡≡-elim



-- data _⊢_ : (n : ℕ) → Exp n → Set
--     var_ : (i : ℕ) → i ≤ n → n ⊢ (var i) 
--     -- every variable is a term
--    --  zero : 
--    --  suc : 
--    --  _+_ : 
--    --  _*_ :











-- Propositions as types in predicate logic
-- sorts
-- termspredicate ϕ(t) formula where t is term (expression)
-- unit form t = unicodeprimitive predicate

-- adding ∀ and ∃ - they are dependent on terms!
-- x₁:A₁...xₙ:Aₙ ⊢ ϕ(x₁...xₙ)
-- t =ₐ u .. identitiy type
-- ∀ x ∈ A ϕ(x) ... Π(x∈A)ϕ(x)      video: 
-- ∃_                ∑              video: 1h 30min

-- context: Γ = x₁:A₁...xₙ:Aₙć
--          Δ = ϕ₁ ... ϕₙ

-- formula ϕ is a logical statement
-- ϕ is provable is not the same as stating that p is a proof of ϕ
-- ϕ should have at least one let
-- the elements of ϕ are the proofs


   




      