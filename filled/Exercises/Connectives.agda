{-# OPTIONS --allow-unsolved-metas #-}
module Exercises.Connectives where

-- Library

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)

-- you may import more, as needed
open import Isomorphism using (extensionality; _≃_; _≲_; _⇔_)
open import Connectives

-- 747/PLFA exercise: IffIsoIfOnlyIf (1 point)
-- Show A ⇔ B is isomorphic to (A → B) × (B → A).

iff-iso-if-onlyif : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
iff-iso-if-onlyif = {!!}

-- 747/PLFA exercise: SumCommIso (1 point)
-- Sum is commutative up to isomorphism.

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm = {!!}

-- 747/PLFA exercise: SumAssocIso (1 point)
-- Sum is associative up to isomorphism.

⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc = {!!}

-- 747/PLFA exercise: EmptyLeftIdSumIso (1 point)
-- Empty is the left unit of sum up to isomorphism.

⊎-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊎-identityˡ = {!!}

-- 747/PLFA exercise: EmptyRightIdSumIso (1 point)
-- Empty is the right unit of sum up to isomorphism.

⊎-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊎-identityʳ = {!!}

-- PLFA exercise: a weak distributive law.
-- ⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
-- ⊎-weak-× A⊎B×C = {!!}
-- State and prove the strong law, and explain the relationship.

-- 747/PLFA exercise: SumOfProdImpProdOfSum (1 point)
-- A disjunct of conjuncts implies a conjunct of disjuncts.

⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ A×B⊎C×D = {!!}

-- PLFA exercise: Is the converse true? If so, prove it; if not, give a counterexample.

-- See PLFA for a number of slight differences with the standard library.

-- Unicode introduced in this chapter:

{-

  ×  U+00D7  MULTIPLICATION SIGN (\x)
  ⊎  U+228E  MULTISET UNION (\u+)
  ⊤  U+22A4  DOWN TACK (\top)
  ⊥  U+22A5  UP TACK (\bot)
  η  U+03B7  GREEK SMALL LETTER ETA (\eta)
  ₁  U+2081  SUBSCRIPT ONE (\_1)
  ₂  U+2082  SUBSCRIPT TWO (\_2)
  ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>, \iff, \lr=)

-}
