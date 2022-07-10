-- TO POBRIŠI KO BO V TEJ DATOTEKI VSE NAREJENO
-- {-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin using (Fin)
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Function.Equivalence using (_⇔_)
open import Function

-- https://agda.github.io/agda-stdlib/

open import NaturalDeduction

module Semantics where

--========================= VALUATIONS ===================================================

  -- a valuation assigns a number to each variable
  Valuation : ℕ → Set
  Valuation n = Fin n → ℕ

  -- we want a function that takes Valuation n and returns Valutation suc n
  Ext-valuation : ∀ {n : ℕ} → Valuation n → ℕ → Valuation (suc n)
  Ext-valuation η n Fin.zero = n
  Ext-valuation η n (Fin.suc x) = η x

--================================== INTERPRETATION ===========================================

  -- the meaning of an expression is a number
  -- ⟦ ⟧ dobimo z \[[ in \]]
  ⟦_⟧ᵉ : {n : ℕ} → Exp n → Valuation n  → ℕ
  ⟦ var x ⟧ᵉ η = η x                           --- η dobimo z \eta
  ⟦ zeroᴾ ⟧ᵉ η = 0
  ⟦ sucᴾ t ⟧ᵉ η = suc (⟦ t ⟧ᵉ η)
  ⟦ s +ᴾ t ⟧ᵉ η = (⟦ s ⟧ᵉ η) + (⟦ t ⟧ᵉ η)
  ⟦ s *ᴾ t ⟧ᵉ η = (⟦ s ⟧ᵉ η) * (⟦ t ⟧ᵉ η)



  ⟦_⟧ᶠ : {n : ℕ} → Formula n → Valuation n  → Set
  ⟦ ⊤ᵖ ⟧ᶠ η = ⊤
  ⟦ ⊥ᵖ ⟧ᶠ η = ⊥
  ⟦ φ ∧ᵖ ψ ⟧ᶠ η = ⟦ φ ⟧ᶠ η × ⟦ ψ ⟧ᶠ η
  ⟦ φ ∨ᵖ ψ ⟧ᶠ η = ⟦ φ ⟧ᶠ η ⊎ ⟦ ψ ⟧ᶠ η
  ⟦ φ ⇒ᵖ ψ ⟧ᶠ η = (⟦ φ ⟧ᶠ η) → (⟦ ψ ⟧ᶠ η)
  ⟦ ∀ᵖ φ ⟧ᶠ η =  (x : ℕ) → ⟦ φ ⟧ᶠ (Ext-valuation η x)
  ⟦ ∃ᵖ φ ⟧ᶠ η = Σ[ x ∈ ℕ ] ⟦ φ ⟧ᶠ (Ext-valuation η x)
  ⟦ t ≈ᵖ u ⟧ᶠ η = ⟦ t ⟧ᵉ η ≡ ⟦ u ⟧ᵉ η


  ⟦_⟧ʰ : {n : ℕ} → Hypotheses n → Valuation n → Set
  ⟦ [] ⟧ʰ η = ⊤
  ⟦ Ψ ∷ Δ ⟧ʰ η = ⟦ Ψ ⟧ᶠ η × ⟦ Δ ⟧ʰ η


  -- project a hypothesis (for soundness of hyp)
  proj-hypothesis : {n : ℕ} {Δ : Hypotheses n} {η : Valuation n} {φ : Formula n} →
                    ⟦ Δ ⟧ʰ η → φ ∈ Δ → ⟦ φ ⟧ᶠ η
  proj-hypothesis H ∈-here = proj₁ H
  proj-hypothesis H ∈-there = proj-hypothesis (proj₂ H) _

  --- (for soundness of p-zero)
  proj-last-hypothesis : {n : ℕ} {Δ : Hypotheses n} {η : Valuation n} {φ : Formula n} → ⟦ Δ ⟧ʰ η → ⟦ φ ⟧ᶠ η
  proj-last-hypothesis {Δ = x ∷ []} H = {!   !}
  proj-last-hypothesis {Δ = []}  H = {! !}
  proj-last-hypothesis {Δ = _ ∷ Δ} (x , H) = proj-last-hypothesis H



  unshift-formula : {n k : ℕ} {φ : Formula n} {η : Valuation n} → ⟦ shift-Formula φ ⟧ᶠ (Ext-valuation η k) → ⟦ φ ⟧ᶠ η
  unshift-formula p = {! !}

  unext-val : ∀ {n : ℕ} → Valuation (suc n) → ℕ → Valuation n 
  unext-val {n = k} η n = {!   !}

  --unshift-val :  ⟦ φ ⟧ᶠ (Ext-valuation η x) →  ⟦ φ ⟧ᶠ η

  -- shift-expression : {n k : ℕ} {t : Exp n} {η : Valuation n} → Exp n → ⟦ shift-Exp t ⟧ᵉ (Ext-valuation η k)
  -- shift-expression t = ?

  shift-formula : {n k : ℕ} {φ : Formula n} {η : Valuation n} → ⟦ φ ⟧ᶠ η → ⟦ shift-Formula φ ⟧ᶠ (Ext-valuation η k)
  shift-formula {φ = ⊤ᵖ} p = tt
  shift-formula {φ = φ ∧ᵖ ψ} (p₁ , p₂) = (shift-formula p₁) , (shift-formula p₂) 
  shift-formula {φ = φ ∨ᵖ ψ} (inj₁ x) = inj₁ (shift-formula x)
  shift-formula {φ = φ ∨ᵖ ψ} (inj₂ y) = inj₂ (shift-formula y)
  shift-formula {φ = φ ⇒ᵖ ψ} p = λ x → shift-formula (p (unshift-formula x))
  shift-formula {φ = ∀ᵖ φ} p = λ x → {! shift-formula (p x)  !} -- instead of (Ext-valuation (Ext-valuation η k) x) this shift-formula (p x)  gives us (Ext-valuation (Ext-valuation η x) k)
  shift-formula {φ = ∃ᵖ φ} (k , p) = k , {!!}
  shift-formula {φ = x ≈ᵖ y} p = {!!}


  shift-hypotheses : {n k : ℕ} {Δ : Hypotheses n} {η : Valuation n} → ⟦ Δ ⟧ʰ η → ⟦ shift-Hypos Δ ⟧ʰ (Ext-valuation η k)
  shift-hypotheses {Δ = []} H = tt
  shift-hypotheses {Δ = φ ∷ Δ} {η = η} H = shift-formula (proj₁ H) , shift-hypotheses (proj₂ H)

  last-hypothesis : {n : ℕ} (Δ : Hypotheses n) → Formula n 
  last-hypothesis [] = ⊥ᵖ
  last-hypothesis (x ∷ []) = x
  last-hypothesis (x ∷ xs) = last-hypothesis xs

  
  -- extend by one mpre hypotheses
  extend : {n : ℕ} {Δ : Hypotheses n} {η : Valuation n} {φ : Formula n} → ⟦ Δ ⟧ʰ η → ⟦ φ ⟧ᶠ η → ⟦ Δ ++ φ ∷ [] ⟧ʰ η
  extend {Δ = []} H y = y , tt
  extend {Δ = _ ∷ Δ} (x , H) y = x , extend H y


  lemma-subst₀ : {n : ℕ} {η : Valuation n} {φ : Formula (suc n)} {t : Exp n} →
                 ⟦ subst-Formula (subst₀ t) φ ⟧ᶠ η ≡ ⟦ φ ⟧ᶠ (Ext-valuation η (⟦ t ⟧ᵉ η))
  lemma-subst₀ = {!!}

  convert : {X Y : Set} → X ≡ Y → X → Y
  convert refl x = x

  --================================= SOUNDNESS ==================================================

  soundness : {n : ℕ} (Δ : Hypotheses n)
          → {φ : Formula n}
          → (n , Δ  ⊢ φ)
          → (η : Valuation n)
          → ⟦ Δ ⟧ʰ η
          → ⟦ φ ⟧ᶠ η

  -- Δ hypotheses
  -- (...) formula
  -- η valuation
  -- H interpretation of hypotheses

  -- hypotheses
  soundness Δ (hyp φ x) η H = proj-hypothesis H x


  -- booleans
  soundness Δ ⊤ᵖ-intro η H = tt
  soundness Δ (⊥ᵖ-elim P) η H = ⊥-elim (soundness Δ P η H)
  --⊥-elim : ∀ {w} {Whatever : Set w} → ⊥ → Whatever


  -- conjunction
  soundness Δ (∧-intro P Q) η H = (soundness Δ P η H) , (soundness Δ Q η H)
  soundness Δ (∧-elim₁ P) η H = proj₁ (soundness Δ P η H)
  soundness Δ (∧-elim₂ P) η H = proj₂ (soundness Δ P η H)


  -- disjunction
  soundness Δ (∨-intro₁ P) η H = inj₁ (soundness Δ P η H) 
  soundness Δ (∨-intro₂ P) η H = inj₂ (soundness Δ P η H)
  soundness Δ (∨-elim {φ₁ = φ₁} {φ₂ = φ₂} P Q R) η H = [ (λ x →  soundness (Δ ++ φ₁ ∷ []) Q η (extend H x)) , ((λ x →  soundness (Δ ++ φ₂ ∷ []) R η (extend H x))) ]′ (soundness Δ P η H)


  -- implication
  soundness Δ (⇒-intro {φ = φ} P) η H = λ x → soundness (Δ ++ φ ∷ []) P η (extend H x)
  soundness Δ (⇒-elim P Q) η H =
      modus-ponens (soundness Δ P η H) (soundness Δ Q η H)
          where
              modus-ponens : ∀ {A B : Set} → (A → B) → A → B
              modus-ponens x y = x y
              -- not necessary but shows how this works


  -- ∀ᵖ
  soundness Δ (∀ᵖ-elim t P) η H = {!!} -- for ∀ᵖ prod and sigmas
  soundness Δ (∀ᵖ-intro x) η H = λ y → soundness (shift-Hypos Δ) x (Ext-valuation η y) (shift-hypotheses H) -- looks suspiciously easy


  -- ∃ᵖ
  soundness Δ (∃ᵖ-intro x P) η H = {!   !} , {!   !}

  soundness Δ (∃ᵖ-elim {n = n} {φ = φ} {ψ = ψ} P Q) η H = unshift-formula (soundness _ Q (Ext-valuation η a) H')
    where
      a : ℕ
      a = proj₁ (soundness Δ P η H)

      shifted-H : ⟦ shift-Hypos Δ ⟧ʰ (Ext-valuation η a)
      shifted-H = shift-hypotheses H

      H' : ⟦ shift-Hypos Δ ++ NaturalDeduction.[ φ ] ⟧ʰ (Ext-valuation η a)
      H' = extend shifted-H (proj₂ (soundness Δ P η H))

 
 
  -- equality
  soundness Δ (≈-refl t) η H = refl -- surprisingly
  soundness Δ (≈-subt P Q) η H = subst {!  !} {!  !} {!    !}
  soundness Δ (≈-sym P) η H = sym (soundness Δ P η H)
  soundness Δ (≈-trans P Q) η H = trans (soundness Δ P η H) (soundness Δ Q η H)


  -- peano
  soundness Δ p-zero η H = 1+n≢0 {!  !}
  soundness Δ (p-suc P) η H = cong-suc (soundness Δ P η H)
                                  where
                                      cong-suc : {x y : ℕ} → (suc x) ≡ (suc y) → x ≡ y
                                      cong-suc refl = refl
  soundness Δ (p-sum) η P = refl
  soundness Δ p-sumsuc η P = refl
  soundness Δ p-prod η P = refl
  soundness Δ p-prodsum η P = refl

  soundness Δ (p-induc {φ = φ} t P Q) η H = convert (sym (lemma-subst₀)) p
    where
      loop : (k : ℕ) → ⟦ φ ⟧ᶠ (Ext-valuation η k)
      loop zero = {!!}
      loop (suc n) = {!!}

      p : ⟦ φ ⟧ᶠ (Ext-valuation η (⟦ t ⟧ᵉ η))
      p = loop (⟦ t ⟧ᵉ η)
  