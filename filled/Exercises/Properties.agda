{-# OPTIONS --allow-unsolved-metas #-}
module Exercises.Properties where

-- Library

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no; does; proof; _because_; ofʸ; ofⁿ)
open import Agda.Builtin.Bool using (true; false)
open import Function using (_∘_)

open import Isomorphism using (_≃_)
open import Lambda
open import Properties

-- 747/PLFA exercise: AltProg (5 points)
-- Here is an alternate formulation of progress.
-- Show that it is isomorphic to Progress M, and prove this form
-- of the progress theorem directly.

progress-iso : ∀ {M} → Progress M ≃ Value M ⊎ ∃[ N ](M —→ N)
progress-iso = {!!}

progress′ : ∀ M {A} → ∅ ⊢ M ⦂ A → Value M ⊎ ∃[ N ](M —→ N)
progress′ m m:a = {!!}

-- 747/PLFA exercise: ValueEh (1 point)
-- Write a function to decide whether a well-typed term is a value.
-- Hint: reuse theorems proved above to do most of the work.

value? : ∀ {A M} → ∅ ⊢ M ⦂ A → Dec (Value M)
value? m:a = {!!}

-- 747/PLFA exercise: Unstuck (3 points)
-- Using progress and preservation, prove the following:

unstuck : ∀ {M A} → ∅ ⊢ M ⦂ A → ¬ (Stuck M)
unstuck m:a = {!!}

preserves : ∀ {M N A} → ∅ ⊢ M ⦂ A → M —↠ N → ∅ ⊢ N ⦂ A
preserves m:a msn = {!!}

wttdgs : ∀ {M N A} → ∅ ⊢ M ⦂ A → M —↠ N → ¬ (Stuck N)
wttdgs m:a msn = {!!}
