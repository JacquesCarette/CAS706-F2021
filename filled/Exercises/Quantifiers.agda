{-# OPTIONS --allow-unsolved-metas #-}
module Exercises.Quantifiers where

-- Library

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s) -- added ≤
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩) -- added proj₂
open import Data.Sum using (_⊎_; inj₁; inj₂ ) -- added inj₁, inj₂
open import Function using (_∘_) -- added

open import Isomorphism
open import Quantifiers

-- 747/PLFA exercise: ForAllDistProd (1 point)
-- Show that ∀ distributes over ×.
-- (The special case of → distributes over × was shown in the Connectives chapter.)

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× = {!!}

-- 747/PLFA exercise: SumForAllImpForAllSum (1 point)
-- Show that a disjunction of foralls implies a forall of disjunctions.

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ ∀B⊎∀C = {!!}

-- 747/PLFA exercise: ExistsDistSum (2 points)
-- Show that existentials distribute over disjunction.

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ = {!!}

-- 747/PLFA exercise: ExistsProdImpProdExists (1 point)
-- Show that existentials distribute over ×.

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ = {!!}

-- 747/PLFA exercise: AltLE (3 points)
-- An alternate definition of y ≤ z.

∃-≤ : ∀ {y z : ℕ} → ( (y ≤ z) ⇔ ( ∃[ x ] (y + x ≡ z) ) )
∃-≤ = {!!}

-- 747/PLFA exercise: ExistsNegImpNegForAll (1 point)
-- Existence of negation implies negation of universal.

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    --------------
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ ∃¬B = {!!}

-- The converse cannot be proved in intuitionistic logic.
