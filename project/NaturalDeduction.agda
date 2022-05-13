
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
    `_ : Fin n → Exp n -- expression with n variables
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
--   ∀∀_ : Formula (suc n) → Formula n                 -- for all
--   ∃_ : Formula (suc n) → Formula n                   -- exists :(
--   _≡≡_ : Exp n → Exp n → Formula n

infixr 6 _∧_
infixr 5 _∨_
infixr 4 _⇒_

-- infix 7 ∀∀_
-- infix 8 ∃_


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

-- TODO 

-- DeBrujin indices
--   ∀-intro   : (n : ℕ) → {Δ : Hypotheses n}
            
  

--   ∀-elim

--   ∃-intro

--   ∃-elim

--   ≡≡-intro

--   ≡≡-elim

{-
   We define negation and logical equivalence as syntactic sugar.
   These definitions are standard logical encodings of `¬` and `⇔`.
-}

-- ¬_ : Formula → Formula              -- unicode \neg
-- ¬ φ = φ ⇒ ⊥

-- _⇔_ : Formula → Formula → Formula    -- unicode \<=>
-- φ ⇔ ψ = (φ ⇒ ψ) ∧ (ψ ⇒ φ)

-- infix 7 ¬_
-- infix 3 _⇔_


----------------
-- Exercise 1 --
----------------

{-
   Show that the standard introduction and elimination rules of `¬`
   are derivable for the logical encoding of `¬` defined above.
-}

-- ¬-intro : {Δ : Hypotheses}
--         → {φ : Formula}
--         → Δ ++ [ φ ] ⊢ ⊥
--         → Δ ⊢ ¬ φ

-- ¬-intro d = ⇒-intro d

-- ¬-elim : {Δ : Hypotheses}
--        → {φ : Formula}
--        → Δ ⊢ φ
--        → Δ ⊢ ¬ φ
--        → Δ ⊢ ⊥

-- ¬-elim d₁ d₂ = ⇒-elim d₂ d₁

-- {-
--    Show that the last rule is also derivable when the assumptions
--    about `φ` and `¬ φ` being true are given as part of hypotheses.
-- -}

-- ¬-elim' : (φ : Formula)
--         → [ φ ] ++ [ ¬ φ ] ⊢ ⊥

-- ¬-elim' φ = ⇒-elim (hyp (¬ φ)) (hyp φ)


-- ----------------
-- -- Exercise 2 --
-- ----------------

-- {-
--    Show that the cut rule is derivable in the above natural deduction
--    system (by using the intro/elim-rules of other logical connectives).

--    Note 1: There are more than one possible derivations of the cut rule.

--    Note 2: While here the richness of our logic (i.e., the other logical
--    connectives) allows us to simply **derive** the cut rule as a single
--    concrete derivation, in more general settings one usually shows the
--    **admissibility** of the cut rule by induction on the (heights of)
--    the given derivations, e.g., see https://www.jstor.org/stable/420956.
-- -}

-- cut-derivable : {Δ : Hypotheses}
--               → {φ ψ : Formula}
--               → Δ ⊢ φ
--               → Δ ++ [ φ ] ⊢ ψ
--               ------------------
--               → Δ ⊢ ψ

-- cut-derivable d₁ d₂ = ⇒-elim (⇒-intro d₂) d₁



     