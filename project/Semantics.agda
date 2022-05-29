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

-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl)

open import NaturalDeduction

module Semantics where

  -- a valuation assigns a number to each variable
  Valuation : ℕ → Set
  Valuation n = Fin n → ℕ

  -- we want extended valuation for all and some semantics due to the change in context
  -- to use this in all and some semantics
  Ext-valuation : {n : ℕ} → Valuation n → ℕ → Valuation (suc n)
  Ext-valuation η zero = {!   !}
  Ext-valuation η (suc x) = {!   !}


  -- the meaning of an expression is a number
  -- ⟦ ⟧ dobimo z \[[ in \]]
  ⟦_⟧ᵉ : {n : ℕ} → Exp n → Valuation n  → ℕ
  ⟦ var x ⟧ᵉ η = η x                           --- η dobimo z \eta
  ⟦ zeroᴾ ⟧ᵉ η = 0
  ⟦ sucᴾ t ⟧ᵉ η = suc (⟦ t ⟧ᵉ η)
  ⟦ s +ᴾ t ⟧ᵉ η = (⟦ s ⟧ᵉ η) + (⟦ t ⟧ᵉ η)                               -- a: 
  ⟦ s *ᴾ t ⟧ᵉ η = (⟦ s ⟧ᵉ η) * (⟦ t ⟧ᵉ η)                               -- a: 



  ⟦_⟧ᶠ : {n : ℕ} → Formula n → Valuation n  → Set
  ⟦ ⊤ᵖ ⟧ᶠ η = ⊤
  ⟦ ⊥ᵖ ⟧ᶠ η = ⊥                                                         -- a: 
  ⟦ φ ∧ᵖ ψ ⟧ᶠ η = ⟦ φ ⟧ᶠ η × ⟦ ψ ⟧ᶠ η                                    -- a:  -- from exercises for propositional logic: ⟦ φ ∧ ψ ⟧ η = ⟦ φ ⟧ η and ⟦ ψ ⟧ η
  ⟦ φ ∨ᵖ ψ ⟧ᶠ η = ⟦ φ ⟧ᶠ η ⊎ ⟦ ψ ⟧ᶠ η                                   -- a:
  ⟦ φ ⇒ᵖ ψ ⟧ᶠ η = (⟦ φ ⟧ᶠ η) → (⟦ ψ ⟧ᶠ η)                               -- a: not sure
                                                                        -- A → B : λ (x : A) → N where N is a term of type B containing as a free variable x of type A.
 
 
  ⟦ all φ ⟧ᶠ η =  (x : ℕ) → ⟦ φ ⟧ᶠ (λ { Fin.zero → x; (Fin.suc xs) → η xs }) 
                                      -- this lambda is a valuation

  ⟦ some φ ⟧ᶠ η = Σ[ x ∈ ℕ ] ⟦ φ ⟧ᶠ (λ { Fin.zero → x; (Fin.suc xs) → η xs }) -- not sure
  
                     -- Σ[ x ∈ A ] B x        A (λ x → B) 
  ⟦ φ ≈ᵖ ψ ⟧ᶠ η = ⟦ {!   !} ⟧ᶠ η   
  --  _≈ᵖ_ : Exp n → Exp n → Formula n



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

--   hyp      : (n : ℕ) → {Δ : Hypotheses n}
--            → (φ : Formula n)
--            → (φ ∈ Δ)
--            -----------------
--            → n , Δ ⊢ φ

  soundness Δ (hyp _ _ x) η H = {!!} -- x ni derivation zatu ne moreš na njem delat soundness, x je φ ∈ Δ
  soundness Δ (⊤-intro _) η H = tt
  soundness Δ (⊥ᵖ-elim _ P) η H = ⊥-elim (soundness Δ P η H)                                    -- (alone) not sure
                                -- P : n , Δ ⊢ ⊥ᵖ
  soundness Δ (∧-intro _ P Q) η H = (soundness Δ P η H) , (soundness Δ Q η H)                                                       
  soundness Δ (∧-elim₁ _ P) η H = proj₁ (soundness Δ P η H)                     
  soundness Δ (∧-elim₂ _ P) η H = proj₂ (soundness Δ P η H) 
  soundness Δ (∨-intro₁ _ P) η H = inj₁ (soundness Δ P η H)                                     -- (alone) zakaj se z drugo barvo pobarva kot proj₁? :(
  soundness Δ (∨-intro₂ _ P) η H = inj₂ (soundness Δ P η H)                                     -- (alone)
  soundness Δ (∨-elim _ P Q R) η H = {!!} --((soundness (inj₁ soundness Δ P η H) Q η H) + (soundness (inj₂ soundness Δ P η H) R η H))
        -- ϕ₁ inj₁ soundness p
        -- soundness (Δ ++ (inj₁ soudness Δ P η H)) Q η H  tko bi rekla js za 

  soundness Δ (⇒-intro _ P) η H = {!!}
  soundness Δ (⇒-elim _ P Q) η H = {!!}
  soundness Δ (all-elim _ t P) η H = {!!} -- for all prod and sigmas 
  soundness Δ (≈-refl _ t) η H = {!!}
  soundness Δ (≈-subt _ P Q) η H = {!!}
  soundness Δ (≈-suc _ P) η H = {!!}
  soundness Δ (all-intro _ x) η P = {!   !}
  soundness Δ (some-intro _ x) η P = {!   !}
  soundness Δ (some-elim _ x x₁) η P = {!   !}
  soundness Δ (≈-sym _ x) η P = {!   !}
  soundness Δ (≈-trans _ x x₁) η P = {!   !}
  soundness Δ (≈-sum _) η P = {!   !}
  soundness Δ (≈-sumsuc _) η P = {!   !}
  soundness Δ (≈-prod _) η P = {!   !}
  soundness Δ (≈-prodsum _) η P = {!   !}
 
 