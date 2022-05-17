open import Data.Nat
open import Data.Fin using (Fin)
open import Data.Unit
open import Data.Product

open import NaturalDeduction

module Semantics where

  -- a valuation assigns a number to each variable
  Valuation : ℕ → Set
  Valuation n = Fin n → ℕ

  -- the meaning of an expression is a number
  -- ⟦ ⟧ dobimo z \[[ in \]]
  ⟦_⟧ᵉ : {n : ℕ} → Exp n → Valuation n  → ℕ
  ⟦ var x ⟧ᵉ η = η x
  ⟦ zeroᴾ ⟧ᵉ η = 0
  ⟦ sucᴾ t ⟧ᵉ η = suc (⟦ t ⟧ᵉ η)
  ⟦ t +ᴾ t₁ ⟧ᵉ η = {!!}
  ⟦ t *ᴾ t₁ ⟧ᵉ η = {!!}

  ⟦_⟧ᶠ : {n : ℕ} → Formula n → Valuation n  → Set
  ⟦ ⊤ᵖ ⟧ᶠ η = ⊤
  ⟦ ⊥ ⟧ᶠ η = {!!}
  ⟦ φ ∧ Ψ ⟧ᶠ η = ⟦ φ ⟧ᶠ η ×  ⟦ Ψ ⟧ᶠ η
  ⟦ φ ∨ φ₁ ⟧ᶠ η = {!!}
  ⟦ φ ⇒ φ₁ ⟧ᶠ η = {!!}
  ⟦ all φ ⟧ᶠ η = {!!}
  ⟦ some φ ⟧ᶠ η = {!!}
  ⟦ s ≈ t ⟧ᶠ η = {!!}

  ⟦_⟧ʰ : {n : ℕ} → Hypotheses n → Valuation n → Set
  ⟦ [] ⟧ʰ η =  ⊤
  ⟦ Ψ ∷ Δ ⟧ʰ η = ⟦ Ψ ⟧ᶠ η × ⟦ Δ ⟧ʰ η

  -- soundness
  sound : {n : ℕ} (Δ : Hypotheses n) → {φ : Formula n} →
          (n , Δ  ⊢ φ) → (η : Valuation n) → ⟦ Δ ⟧ʰ η → ⟦ φ ⟧ᶠ η
  sound Δ (hyp _ _ x) η H = {!!}
  sound Δ (⊤-intro _) η H = tt
  sound Δ (⊥-elim _ P) η H = {!!}
  sound Δ (∧-intro _ P Q) η H = (sound Δ P η H) , {!!}
  sound Δ (∧-elim₁ _ P) η H = {!!}
  sound Δ (∧-elim₂ _ P) η H = {!!}
  sound Δ (∨-intro₁ _ P) η H = {!!}
  sound Δ (∨-intro₂ _ P) η H = {!!}
  sound Δ (∨-elim _ P Q R) η H = {!!}
  sound Δ (⇒-intro _ P) η H = {!!}
  sound Δ (⇒-elim _ P Q) η H = {!!}
  sound Δ (all-elim _ t P) η H = {!!}
  sound Δ (≈-refl _ t) η H = {!!}
  sound Δ (≈-subt _ P Q) η H = {!!}
  sound Δ (≈-suc _ P) η H = {!!}
