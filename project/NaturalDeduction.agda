-- TO POBRIŠI KO BO V TEJ DATOTEKI VSE NAREJENO
{-# OPTIONS --allow-unsolved-metas #-}


module NaturalDeduction where

open import Data.List  using (List; []; _∷_; [_]; _++_) public
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Fin using (Fin)
open import Data.Unit

{-From lectures:

The language of a first-order theory is described by a signature, which consists of:
- a list of function symbols fᵢ each of which has an arity nᵢ ∈ ℕ,
- a list of relation symbols Rᵢ each of which has an arity kⱼ ∈ ℕ.
-}

{-
   Basis for formulae taken from lectures and exercises on propositional logic.
   
   Propositional logic consists of statements that can be given a truth value.
   In predicate logic we introduce the concept of a variable and predicates which can have different # of variables. 

   The main building blocks of predicate logic are 
   - terms : expressions that denote the objects we are talking about (zero, suc..)
   - formulas : they denote the truth values

   They are all given a context of variables represented by the number of variables (that are not named)
-}

data Exp (n : ℕ) : Set where
    var_ : Fin n → Exp n
    zeroᴾ : Exp n 
    sucᴾ : Exp n → Exp n
    _+ᴾ_ : Exp n → Exp n → Exp n
    _*ᴾ_ : Exp n → Exp n → Exp n


data Formula (n : ℕ) : Set where
  ⊤ᵖ   : Formula n                                      -- truth (unicode \top)
  ⊥ᵖ   : Formula n                                      -- falsehood (unicode \bot)
  _∧ᵖ_ : Formula n → Formula n → Formula n              -- conjunction (unicode \wedge)
  _∨ᵖ_ : Formula n → Formula n → Formula n              -- disjunction (unicode \vee)
  _⇒ᵖ_ : Formula n → Formula n → Formula n              -- implication (unicode \=>)
  all_ : Formula (suc n) → Formula n                    -- for all \forall\forall
  some_ : Formula (suc n) → Formula n                   -- exists \exists
  _≈ᵖ_ : Exp n → Exp n → Formula n                      -- ≈ᵖ is \approx


infixr 6 _∧ᵖ_
infixr 5 _∨ᵖ_
infixr 4 _⇒ᵖ_

infix 3 all_
infix 3 some_

{- 
Substitutions

For terms (expressions) and formulas we define:
- substitution 
       - for expressions : takes the substitution (n, m) and an expression in n variables and returns an expression in m variables
       - for formulas : takes the substitution (n, m) and a formula in n variables and returns a formula in m variables
- shift
       - for expressions : shifts the expression from Exp n to Exp suc n
       - for formulas : shifts the formula from Formula n to Formula m
       - for substitutions : shifts the substitution from Sub m n to Sub (suc m) (suc n)
-}

-- Sub n m is a function!
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
shift-Formula ⊤ᵖ = ⊤ᵖ
shift-Formula ⊥ᵖ = ⊥ᵖ
shift-Formula (Ψ ∧ᵖ Θ) = (shift-Formula Ψ) ∧ᵖ (shift-Formula Θ)
shift-Formula (Ψ ∨ᵖ Θ) = (shift-Formula Ψ) ∨ᵖ (shift-Formula Θ)
shift-Formula (Ψ ⇒ᵖ Θ) = (shift-Formula Ψ) ⇒ᵖ (shift-Formula Θ)
shift-Formula (all Ψ) = all (shift-Formula Ψ)
shift-Formula (some Ψ) = some (shift-Formula Ψ)
shift-Formula (t ≈ᵖ u) = (shift-Exp t) ≈ᵖ (shift-Exp u)

-- Sub n m = Fin n → Exp m
shift : {n m : ℕ} → Sub n m → Sub (suc n) (suc m)
shift σ Fin.zero = var Fin.zero
shift σ (Fin.suc x) = shift-Exp (σ x)

subst-Formula : {n m : ℕ} → Sub n m → Formula n → Formula m
subst-Formula σ ⊤ᵖ = ⊤ᵖ
subst-Formula σ ⊥ᵖ = ⊥ᵖ
subst-Formula σ (Ψ ∧ᵖ Θ) = subst-Formula σ Ψ ∧ᵖ subst-Formula σ Θ
subst-Formula σ (Ψ ∨ᵖ Θ) = subst-Formula σ Ψ ∨ᵖ subst-Formula σ Θ 
subst-Formula σ (Ψ ⇒ᵖ Θ) = subst-Formula σ Ψ ⇒ᵖ subst-Formula σ Θ 
subst-Formula σ (all Ψ) = all (subst-Formula (shift σ) Ψ) 
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
   From exercises : 

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


-- shift all the formulas in hypotheses from Formula n to Formula suc n
shift-Hypos : {n : ℕ} → Hypotheses n → Hypotheses (suc n)
shift-Hypos [] = []
shift-Hypos (x ∷ Δ) = (shift-Formula x) ∷ shift-Hypos Δ


infixl 2 _,_⊢_
data _,_⊢_ : (n : ℕ) → (Δ : Hypotheses n) → (φ : Formula n) → Set where    -- unicode \vdash


  -- basis taken from exercises, added context of n variables

  -- hypotheses

  hyp      : {n : ℕ} → {Δ : Hypotheses n}
           → (φ : Formula n)
           → (φ ∈ Δ)
           -----------------
           → n , Δ ⊢ φ

  -- truth

  ⊤ᵖ-intro  : {n : ℕ} → {Δ : Hypotheses n}
           ------------------
           → n , Δ ⊢ ⊤ᵖ

  -- falsehood

  ⊥ᵖ-elim   : {n : ℕ} → {Δ : Hypotheses n}
           → {φ : Formula n}
           → n , Δ ⊢ ⊥ᵖ
           -------------------
           → n , Δ ⊢ φ

  -- conjunction

  ∧-intro  : {n : ℕ} → {Δ : Hypotheses n}
           → {φ ψ : Formula n}
           → n , Δ ⊢ φ
           → n , Δ ⊢ ψ
           -------------------
           → n , Δ ⊢ φ ∧ᵖ ψ

  ∧-elim₁  : {n : ℕ} → {Δ : Hypotheses n}
           → {φ ψ : Formula n}
           → n , Δ ⊢ φ ∧ᵖ ψ
           -------------------
           → n , Δ ⊢ φ

  ∧-elim₂  : {n : ℕ} → {Δ : Hypotheses n}
           → {φ ψ : Formula n}
           → n , Δ ⊢ φ ∧ᵖ ψ
           -------------------
           → n , Δ ⊢ ψ

  -- disjunction

  ∨-intro₁ : {n : ℕ} → {Δ : Hypotheses n}
           → {φ ψ : Formula n}
           → n , Δ ⊢ φ
           ------------------
           → n , Δ ⊢ φ ∨ᵖ ψ

  ∨-intro₂ : {n : ℕ} → {Δ : Hypotheses n}
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

  ⇒-intro  : {n : ℕ} → {Δ : Hypotheses n}
           → {φ ψ : Formula n}
           → n , Δ ++ [ φ ] ⊢ ψ
           --------------------
           → n , Δ ⊢ φ ⇒ᵖ ψ

  ⇒-elim   : {n : ℕ} → {Δ : Hypotheses n}
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
          → n , Δ ⊢ subst-Formula (subst₀ t) φ  -- subst₀ t ≈ Sub (suc n) n 


  all-intro : {n : ℕ} → {Δ : Hypotheses n} 
           → {φ : Formula (suc n)} 
           → suc n , shift-Hypos Δ ⊢ φ
         --------------------------
           → n , Δ ⊢ all φ


  some-intro : {n : ℕ} → {Δ : Hypotheses n} 
            → {φ : Formula (suc n)}
            → (t : Exp n)
            → n , Δ ⊢ subst-Formula (subst₀ t) φ  -- φ[t/y]
            -------------------------------------
            → n , Δ ⊢ some φ

  some-elim : {n : ℕ} → {Δ : Hypotheses n} 
            → {φ : Formula (suc n)}
            → {ψ : Formula n}
            → n , Δ ⊢ some φ
            → suc n , shift-Hypos Δ ++ [ φ ] ⊢ shift-Formula ψ
            -----------------------
            → n , Δ ⊢ ψ


  -- equality

  ≈-refl : {n : ℕ} → {Δ : Hypotheses n}
         → (t : Exp n)
         -------------
         → n , Δ ⊢ t ≈ᵖ t


  ≈-subt : {n : ℕ} → {Δ : Hypotheses n}
         → {φ : Formula (suc n)}
         → {t u : Exp n}
         → n , Δ ⊢ subst-Formula (subst₀ t) φ
         → n , Δ ⊢ t ≈ᵖ u
         -----------------------
         → n , Δ ⊢ subst-Formula (subst₀ u) φ

  ≈-sym : {n : ℕ} → {Δ : Hypotheses n}
         → {t u : Exp n}
         → n , Δ ⊢ t ≈ᵖ u
         -----------------
         → n , Δ ⊢ u ≈ᵖ t

  ≈-trans : {n : ℕ} → {Δ : Hypotheses n}
         → {t u s : Exp n}
         → n , Δ ⊢ s ≈ᵖ t
         → n , Δ ⊢ t ≈ᵖ u
         -----------------
         → n , Δ ⊢ s ≈ᵖ u

  -- Peano axioms

  -- source: http://www.andrej.com/zapiski/ISRM-LOGRAC-2022/05-logic.lagda.html

  -- first : no succesor is equal to zero
  p-zero : {n : ℕ} → {Δ : Hypotheses n} 
         → {t : Exp n}
         -----------------------
         →  n , Δ ++ [ sucᴾ t ≈ᵖ zeroᴾ ] ⊢ ⊥ᵖ


  -- second
  p-suc : {n : ℕ} → {Δ : Hypotheses n}
        → {t u : Exp n}
        → n , Δ ⊢ sucᴾ t ≈ᵖ sucᴾ u
        -----------------------
        → n , Δ ⊢ t ≈ᵖ u

  -- third
  p-sum : {n : ℕ} → {Δ : Hypotheses n}
         → {u : Exp n}
         ------------------------
         → n , Δ ⊢ (zeroᴾ +ᴾ u) ≈ᵖ u

  -- fourth
  p-sumsuc : {n : ℕ} → {Δ : Hypotheses n}
         → {t u : Exp n}
         ------------------------------------
         → n , Δ ⊢ ((sucᴾ t) +ᴾ u) ≈ᵖ sucᴾ (t +ᴾ u)

   -- fifth
  p-prod : {n : ℕ} → {Δ : Hypotheses n}
         → {u : Exp n}
         ---------------
         → n , Δ ⊢ (zeroᴾ *ᴾ u) ≈ᵖ zeroᴾ

  -- sixth
  p-prodsum : {n : ℕ} → {Δ : Hypotheses n}
         → {t u : Exp n}
         ------------------
         → n , Δ ⊢ ((sucᴾ t) *ᴾ u) ≈ᵖ (u +ᴾ (t *ᴾ u))

  -- seventh
  p-induc : {n : ℕ} → {Δ : Hypotheses n}
         → {φ : Formula (suc n)}
         → (t : Exp n)
         → n , Δ ⊢ subst-Formula (subst₀ zeroᴾ) φ
         → suc n , shift-Hypos Δ ++ [ φ ]  ⊢ subst-Formula (subst'₀ (sucᴾ (var Fin.zero))) φ
         -------------------
         → n , Δ ⊢ subst-Formula (subst₀ t) φ


