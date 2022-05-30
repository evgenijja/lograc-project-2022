
{-
   Allowing overlapping instances for `∈` to use in `hyp`.

   Warning: If used carelessly, could lead to exponential
   slowdown and looping behaviour during instance search.
-}

{-
   Notice that we parametrise the deeply embedded propositional logic
   and its natural deduction proof system over a type of atomic formulaes.
-}

-- TO POBRIŠI KO BO V TEJ DATOTEKI VSE NAREJENO
{-# OPTIONS --allow-unsolved-metas #-}


module NaturalDeduction where

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
    zeroᴾ : Exp n -- expression with n variables (not necessarily all of them)
    -- x + y is an expression in x, y, z
    sucᴾ : Exp n → Exp n
    _+ᴾ_ : Exp n → Exp n → Exp n
    _*ᴾ_ : Exp n → Exp n → Exp n

data Formula (n : ℕ) : Set where
--   `_  : AtomicFormula → Formula n          -- atomic formula
  ⊤ᵖ   : Formula n                          -- truth (unicode \top)
  ⊥ᵖ   : Formula n                          -- falsehood (unicode \bot)
  _∧ᵖ_ : Formula n → Formula n → Formula n       -- conjunction (unicode \wedge)
  _∨ᵖ_ : Formula n → Formula n → Formula n       -- disjunction (unicode \vee)
  _⇒ᵖ_ : Formula n → Formula n → Formula n       -- implication (unicode \=>)
  all_ : Formula (suc n) → Formula n                 -- for all \forall\forall
  some_ : Formula (suc n) → Formula n                   -- exists \exists
  _≈ᵖ_ : Exp n → Exp n → Formula n -- ≈ᵖ is \approx


infixr 6 _∧ᵖ_
infixr 5 _∨ᵖ_
infixr 4 _⇒ᵖ_

infix 3 all_
infix 3 some_

-- Substitution

Sub : ℕ → ℕ → Set
Sub n m = Fin n → Exp m

subst-Exp : {n m : ℕ} → Sub n m → Exp n → Exp m
subst-Exp σ (var x) = σ x
subst-Exp σ zeroᴾ = zeroᴾ
subst-Exp σ (sucᴾ t) = sucᴾ (subst-Exp σ t)
subst-Exp σ (s +ᴾ t) = subst-Exp σ s +ᴾ subst-Exp σ t
subst-Exp σ (s *ᴾ t) = subst-Exp σ s *ᴾ subst-Exp σ t

shift-Exp : {n : ℕ} → Exp n → Exp (suc n)
shift-Exp (var x) = var (Fin.suc x)
shift-Exp zeroᴾ = zeroᴾ
shift-Exp (sucᴾ t) = sucᴾ (shift-Exp t)
shift-Exp (s +ᴾ t) = shift-Exp s +ᴾ shift-Exp t
shift-Exp (s *ᴾ t) = shift-Exp s *ᴾ shift-Exp t

shift-Formula : {n : ℕ} → Formula n → Formula (suc n)
shift-Formula = {!!}

shift : {n m : ℕ} → Sub n m → Sub (suc n) (suc m)
shift σ Fin.zero = var Fin.zero
shift σ (Fin.suc x) = shift-Exp (σ x)

subst-Formula : {n m : ℕ} → Sub n m → Formula n → Formula m
subst-Formula σ ⊤ᵖ = ⊤ᵖ
subst-Formula σ ⊥ᵖ = ⊥ᵖ
subst-Formula σ (Ψ ∧ᵖ Θ) = subst-Formula σ Ψ ∧ᵖ subst-Formula σ Θ
subst-Formula σ (Ψ ∨ᵖ Θ) = subst-Formula σ Ψ ∨ᵖ subst-Formula σ Θ -- a
subst-Formula σ (Ψ ⇒ᵖ Θ) = subst-Formula σ Ψ ⇒ᵖ subst-Formula σ Θ -- a
subst-Formula σ (all Ψ) = all (subst-Formula (shift σ) Ψ) -- a - enako kot some?
subst-Formula σ (some Ψ) = some (subst-Formula (shift σ) Ψ)
subst-Formula σ (s ≈ᵖ t) = (subst-Exp σ s ≈ᵖ subst-Exp σ t)


-- substitute var 0 with the given term in one fewer variables
subst₀ : {n : ℕ} → Exp n → Sub (suc n) n
subst₀ t Fin.zero = t
subst₀ t (Fin.suc x) = var x -- var has type Fin n → Exp n similarly as substitution

-- substitute var 0 with the given term in the same number of variables
subst'₀ : {n : ℕ} → Exp (suc n) → Sub (suc n) (suc n)
subst'₀ t Fin.zero = t
subst'₀ t (Fin.suc x) = var (Fin.suc x)

-- Hypotheses are represented as a list of formulae.
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
  ∈-here  : {x : A} → {xs : List A} → x ∈ (x ∷ xs)
  ∈-there : {x y : A} {xs : List A} → {{x ∈ xs}} → x ∈ (y ∷ xs)


shift-Hypos : {n : ℕ} → Hypotheses n → Hypotheses (suc n)
shift-Hypos = {!!}


infixl 2 _,_⊢_
data _,_⊢_ : (n : ℕ) → (Δ : Hypotheses n) → (φ : Formula n) → Set where    -- unicode \vdash


  -- hypotheses

  hyp      : (n : ℕ) → {Δ : Hypotheses n}
           → (φ : Formula n)
           → (φ ∈ Δ)
           -----------------
           → n , Δ ⊢ φ

  -- truth

  ⊤-intro  : {n : ℕ} → {Δ : Hypotheses n}
           ------------------
           → n , Δ ⊢ ⊤ᵖ

  -- falsehood

  ⊥ᵖ-elim   : (n : ℕ) → {Δ : Hypotheses n}
           → {φ : Formula n}
           → n , Δ ⊢ ⊥ᵖ
           -------------------
           → n , Δ ⊢ φ

  -- conjunction

  ∧-intro  : (n : ℕ) → {Δ : Hypotheses n}
           → {φ ψ : Formula n}
           → n , Δ ⊢ φ
           → n , Δ ⊢ ψ
           -------------------
           → n , Δ ⊢ φ ∧ᵖ ψ

  ∧-elim₁  : (n : ℕ) → {Δ : Hypotheses n}
           → {φ ψ : Formula n}
           → n , Δ ⊢ φ ∧ᵖ ψ
           -------------------
           → n , Δ ⊢ φ

  ∧-elim₂  : (n : ℕ) → {Δ : Hypotheses n}
           → {φ ψ : Formula n}
           → n , Δ ⊢ φ ∧ᵖ ψ
           -------------------
           → n , Δ ⊢ ψ

  -- disjunction

  ∨-intro₁ : (n : ℕ) → {Δ : Hypotheses n}
           → {φ ψ : Formula n}
           → n , Δ ⊢ φ
           ------------------
           → n , Δ ⊢ φ ∨ᵖ ψ

  ∨-intro₂ : (n : ℕ) → {Δ : Hypotheses n}
           → {φ ψ : Formula n}
           → n , Δ ⊢ ψ
           -------------------
           → n , Δ ⊢ φ ∨ᵖ ψ

  ∨-elim   : {n : ℕ} → {Δ : Hypotheses n}
           → {φ₁ φ₂ ψ : Formula n}
           → n , Δ ⊢ φ₁ ∨ᵖ φ₂
           → n , Δ ++ [ φ₁ ] ⊢ ψ
           → n , Δ ++ [ φ₂ ] ⊢ ψ
           ---------------------
           → n , Δ ⊢ ψ

  -- implication

  ⇒-intro  : (n : ℕ) → {Δ : Hypotheses n}
           → {φ ψ : Formula n}
           → n , Δ ++ [ φ ] ⊢ ψ
           --------------------
           → n , Δ ⊢ φ ⇒ᵖ ψ

  ⇒-elim   : (n : ℕ) → {Δ : Hypotheses n}
           → {φ ψ : Formula n}
           → n , Δ ⊢ φ ⇒ᵖ ψ
           → n , Δ ⊢ φ
           -------------------
           → n , Δ ⊢ ψ

  -- universal quantifier

  all-elim : {n : ℕ} → {Δ : Hypotheses n}
          → {φ : Formula (suc n)}
          → (t : Exp n)
          → n , Δ ⊢ all φ
          -----------------
          → n , Δ ⊢ subst-Formula (subst₀ t) φ

-- subst₀ : {n : ℕ} → Exp n → Sub (suc n) n
-- subst₀ t Fin.zero = t
-- subst₀ t (Fin.suc x) = var x

  all-intro : {n : ℕ} → {Δ : Hypotheses n} -- govorilna
           → {φ : Formula (suc n)} -- x not in freevariables(Δ)
           → suc n , shift-Hypos Δ ⊢ φ
         --------------------------
           → n , Δ ⊢ all φ -- TODO


  some-intro : {n : ℕ} → {Δ : Hypotheses n} -- a
            → {φ : Formula (suc n)}
            → (t : Exp n)
            → n , Δ ⊢ subst-Formula (subst₀ t) φ  -- φ[t/y]
            -------------------------------------
            → n , Δ ⊢ some φ

  some-elim : {n : ℕ} → {Δ : Hypotheses n} -- govorilna
            → {φ : Formula (suc n)}
            → {ψ : Formula n}
            → n , Δ ⊢ some φ
            → suc n , shift-Hypos Δ ++ [ φ ] ⊢ shift-Formula ψ
            -----------------------
            → n , Δ ⊢ ψ


  -- equality

  ≈-refl : (n : ℕ) → {Δ : Hypotheses n}
         → (t : Exp n)
         -------------
         → n , Δ ⊢ t ≈ᵖ t


  ≈-subt : (n : ℕ) → {Δ : Hypotheses n}
         → {φ : Formula (suc n)}
         → {t u : Exp n}
         → n , Δ ⊢ subst-Formula (subst₀ t) φ
         → n , Δ ⊢ t ≈ᵖ u
         -----------------------
         → n , Δ ⊢ subst-Formula (subst₀ u) φ

  ≈-sym : (n : ℕ) → {Δ : Hypotheses n}
         → {t u : Exp n}
         → n , Δ ⊢ t ≈ᵖ u
         -----------------
         → n , Δ ⊢ u ≈ᵖ t

  ≈-trans : (n : ℕ) → {Δ : Hypotheses n}
         → {t u s : Exp n}
         → n , Δ ⊢ s ≈ᵖ t
         → n , Δ ⊢ t ≈ᵖ u
         -----------------
         → n , Δ ⊢ s ≈ᵖ u

  -- Peano axioms

  -- katere izpeljave manjkajo glej: http://www.andrej.com/zapiski/ISRM-LOGRAC-2022/05-logic.lagda.html


  -- prvi : no succesor is equal to zero
  ≈-zero : {n : ℕ} → {Δ : Hypotheses n} -- govorilna
         → {t : Exp n}
         -----------------------
         →  n , Δ ++ [ sucᴾ t ≈ᵖ zeroᴾ ] ⊢ ⊥ᵖ


  -- drugi
  ≈-suc : {n : ℕ} → {Δ : Hypotheses n}
        → {t u : Exp n}
        → n , Δ ⊢ sucᴾ t ≈ᵖ sucᴾ u
        -----------------------
        → n , Δ ⊢ t ≈ᵖ u

  -- tretji
  ≈-sum : (n : ℕ) → {Δ : Hypotheses n}
         → {u : Exp n}
         ------------------------
         → n , Δ ⊢ (zeroᴾ +ᴾ u) ≈ᵖ u

  -- četrti
  ≈-sumsuc : (n : ℕ) → {Δ : Hypotheses n}
         → {t u : Exp n}
         ------------------------------------
         → n , Δ ⊢ ((sucᴾ t) +ᴾ u) ≈ᵖ sucᴾ (t +ᴾ u)

   -- peti
  ≈-prod : (n : ℕ) → {Δ : Hypotheses n}
         → {u : Exp n}
         ---------------
         → n , Δ ⊢ (zeroᴾ *ᴾ u) ≈ᵖ zeroᴾ

  -- šesti
  ≈-prodsum : (n : ℕ) → {Δ : Hypotheses n}
         → {t u : Exp n}
         ------------------
         → n , Δ ⊢ ((sucᴾ t) *ᴾ u) ≈ᵖ (u +ᴾ (t *ᴾ u))

  -- sedmi
  ≈-induc : {n : ℕ} → {Δ : Hypotheses n} -- govorilna
         → {φ : Formula (suc n)}
         → (t : Exp n)
         → n , Δ ⊢ subst-Formula (subst₀ zeroᴾ) φ
         → suc n , shift-Hypos Δ ++ [ φ ]  ⊢ subst-Formula (subst'₀ (sucᴾ (var Fin.zero))) φ
         -------------------
         → n , Δ ⊢ subst-Formula (subst₀ t) φ


-- subst₀ : {n : ℕ} → Exp n → Sub (suc n) n
-- subst₀ t Fin.zero = t
-- subst₀ t (Fin.suc x) = var x
