-- TO POBRIŠI KO BO V TEJ DATOTEKI VSE NAREJENO
-- {-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat
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
                                                                        
  ⟦ all φ ⟧ᶠ η =  (x : ℕ) → ⟦ φ ⟧ᶠ (Ext-valuation η x)
  --(λ { Fin.zero → x; (Fin.suc xs) → η xs })
  -- this lambda is a valuation

  ⟦ some φ ⟧ᶠ η = Σ[ x ∈ ℕ ] ⟦ φ ⟧ᶠ (λ { Fin.zero → x; (Fin.suc xs) → η xs })
                     -- Σ[ x ∈ A ] B x        A (λ x → B)

  ⟦ t ≈ᵖ u ⟧ᶠ η = ⟦ t ⟧ᵉ η ≡ ⟦ u ⟧ᵉ η
  --  _≈ᵖ_ : Exp n → Exp n → Formula n


  ⟦_⟧ʰ : {n : ℕ} → Hypotheses n → Valuation n → Set
  ⟦ [] ⟧ʰ η = ⊤
  ⟦ Ψ ∷ Δ ⟧ʰ η = ⟦ Ψ ⟧ᶠ η × ⟦ Δ ⟧ʰ η


  -- extend by one mpre hypotheses
  extend : {n : ℕ} {Δ : Hypotheses n} {η : Valuation n} {φ : Formula n} → ⟦ Δ ⟧ʰ η → ⟦ φ ⟧ᶠ η → ⟦ Δ ++ φ ∷ [] ⟧ʰ η
  extend {Δ = []} H y = y , tt
  extend {Δ = _ ∷ Δ} (x , H) y = x , extend H y


  --================================= SOUNDNESS ==================================================

  -- govorilna

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

  -- Δ hypotheses
  -- (...) formula
  -- η valuation
  -- H interpretation of hypotheses


  -- hypotheses 
  soundness Δ (hyp _ φ x) η H = {!!}


  -- booleans
  soundness Δ ⊤-intro η H = tt
  soundness Δ (⊥ᵖ-elim _ P) η H = ⊥-elim (soundness Δ P η H)
  --⊥-elim : ∀ {w} {Whatever : Set w} → ⊥ → Whatever 


  -- conjunction                          
  soundness Δ (∧-intro _ P Q) η H = (soundness Δ P η H) , (soundness Δ Q η H)
  soundness Δ (∧-elim₁ _ P) η H = proj₁ (soundness Δ P η H)
  soundness Δ (∧-elim₂ _ P) η H = proj₂ (soundness Δ P η H)


  -- disjunction
  soundness Δ (∨-intro₁ _ P) η H = inj₁ (soundness Δ P η H) -- not sure
  soundness Δ (∨-intro₂ _ P) η H = inj₂ (soundness Δ P η H)
  soundness Δ (∨-elim {φ₁ = φ₁} {φ₂ = φ₂} P Q R) η H = [ (λ x →  soundness (Δ ++ φ₁ ∷ []) Q η (extend H x)) , ((λ x →  soundness (Δ ++ φ₂ ∷ []) R η (extend H x))) ]′ (soundness Δ P η H)
  

  -- implication
  soundness Δ (⇒-intro _ φ ψ P) η H = {!!}
  soundness Δ (⇒-elim _ P Q) η H = 
      modus-ponens (soundness Δ P η H) (soundness Δ Q η H)
          where 
              modus-ponens : ∀ {A B : Set} → (A → B) → A → B
              modus-ponens x y = x y
              -- prepisan →-elim iz https://plfa.github.io/Connectives/


  -- all
  soundness Δ (all-elim t P) η H = {!!} -- for all prod and sigmas
  soundness Δ (all-intro x) η H = {!   !}
  
  
  -- some
  soundness Δ (some-intro _ x) η H = {!   !}
  soundness Δ (some-elim x P) η H = {! soundness ? P ? ?!}


  -- equality
  soundness Δ (≈-refl _ t) η H = refl -- surprisingly
  soundness Δ (≈-subt _ P Q) η H = {!!}
  soundness Δ (≈-sym _ P) η H = sym (soundness Δ P η H)
  soundness Δ (≈-trans _ P Q) η H = trans (soundness Δ P η H) (soundness Δ Q η H)


  -- peano 
  soundness Δ ≈-zero η H = ⊥-elim _ -- goal: ⊥ 
  soundness Δ (≈-suc P) η H = cong-suc (soundness Δ P η H)
                                  where
                                      cong-suc : {x y : ℕ} → (suc x) ≡ (suc y) → x ≡ y
                                      cong-suc refl = refl 
  soundness Δ (≈-sum _) η P = {! refl !}
  soundness Δ (≈-sumsuc _) η P = {!   !}
  soundness Δ (≈-prod _) η P = {!   !}
  soundness Δ (≈-prodsum _) η P = {!   !}
  soundness Δ (≈-induc x y z) η P = {!   !}