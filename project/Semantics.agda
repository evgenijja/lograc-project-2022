-- TO POBRIŠI KO BO V TEJ DATOTEKI VSE NAREJENO
-- {-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat
open import Data.Fin using (Fin)
open import Data.Unit
open import Data.Product
open import Data.Sum 
open import Data.Empty 
open import Function.Equivalence using (_⇔_)
open import Function




open import NaturalDeduction

module Semantics where

  -- a valuation assigns a number to each variable
  Valuation : ℕ → Set
  Valuation n = Fin n → ℕ

  -- the meaning of an expression is a number
  -- ⟦ ⟧ dobimo z \[[ in \]]
  ⟦_⟧ᵉ : {n : ℕ} → Exp n → Valuation n  → ℕ
  ⟦ var x ⟧ᵉ η = η x                           --- η dobimo z \eta
  ⟦ zeroᴾ ⟧ᵉ η = 0
  ⟦ sucᴾ t ⟧ᵉ η = suc (⟦ t ⟧ᵉ η)
  ⟦ s +ᴾ t ⟧ᵉ η = (⟦ s ⟧ᵉ η) + (⟦ t ⟧ᵉ η)                               -- (alone) 
  ⟦ s *ᴾ t ⟧ᵉ η = (⟦ s ⟧ᵉ η) * (⟦ t ⟧ᵉ η)                               -- (alone) 

  ⟦_⟧ᶠ : {n : ℕ} → Formula n → Valuation n  → Set
  ⟦ ⊤ᵖ ⟧ᶠ η = ⊤
  ⟦ ⊥ᵖ ⟧ᶠ η = ⊥                                                         -- (alone) 
  ⟦ φ ∧ᵖ ψ ⟧ᶠ η = ⟦ φ ⟧ᶠ η × ⟦ ψ ⟧ᶠ η                                           -- (alone)  -- from exercises for propositional logic: ⟦ φ ∧ ψ ⟧ η = ⟦ φ ⟧ η and ⟦ ψ ⟧ η
  ⟦ φ ∨ᵖ ψ ⟧ᶠ η = ⟦ φ ⟧ᶠ η ⊎ ⟦ ψ ⟧ᶠ η                                   -- (alone)
  ⟦ φ ⇒ᵖ ψ ⟧ᶠ η = (⟦ φ ⟧ᶠ η) → (⟦ ψ ⟧ᶠ η)                               -- (alone) 
                                                                        -- A → B : λ (x : A) → N where N is a term of type B containing as a free variable x of type A.
  ⟦ all φ ⟧ᶠ η = {!   !} -- Π
  ⟦ some φ ⟧ᶠ η = {!   !} -- ∑
  ⟦ φ ≈ᵖ ψ ⟧ᶠ η = {!!}


  ⟦_⟧ʰ : {n : ℕ} → Hypotheses n → Valuation n → Set
  ⟦ [] ⟧ʰ η = ⊤
  ⟦ Ψ ∷ Δ ⟧ʰ η = ⟦ Ψ ⟧ᶠ η × ⟦ Δ ⟧ʰ η

  -- soundness
  soundness : {n : ℕ} (Δ : Hypotheses n) 
          → {φ : Formula n} 
          → (n , Δ  ⊢ φ) 
          → (η : Valuation n) 
          → ⟦ Δ ⟧ʰ η 
          → ⟦ φ ⟧ᶠ η

  soundness Δ (hyp _ _ x) η H = {!!}
  soundness Δ (⊤-intro _) η H = tt
  soundness Δ (⊥-elim _ P) η H = {!!}
  soundness Δ (∧-intro _ P Q) η H = (soundness Δ P η H) , (soundness Δ Q η H)                                                       
  soundness Δ (∧-elim₁ _ P) η H = proj₁ (soundness Δ P η H)                     
  soundness Δ (∧-elim₂ _ P) η H = proj₂ (soundness Δ P η H) 
  soundness Δ (∨-intro₁ _ P) η H = {!!}
  soundness Δ (∨-intro₂ _ P) η H = {!!}
  soundness Δ (∨-elim _ P Q R) η H = {!!}
  soundness Δ (⇒-intro _ P) η H = {!!}
  soundness Δ (⇒-elim _ P Q) η H = {!!}
  soundness Δ (all-elim _ t P) η H = {!!} -- for all prod and sigmas 
  soundness Δ (≈-refl _ t) η H = {!!}
  soundness Δ (≈-subt _ P Q) η H = {!!}
  soundness Δ (≈-suc _ P) η H = {!!}
