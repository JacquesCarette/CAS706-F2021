module Exercises.Decidable where

-- Library

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym) -- added sym
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using ()
  renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)

open import Isomorphism using (_⇔_)
open import Relations using (_<_; s<s; z<s)

open import Decidable

-- 747/PLFA exercise: DecLT (3 point)
-- Decidable strict equality.
-- You will need these helper functions as we did above.

¬z<z : ¬ (zero < zero)
¬z<z = {!!}

¬s<s : ∀ {m n : ℕ} → ¬ (m < n) → ¬ (suc m < suc n)
¬s<s = {!!}

¬s<z : ∀ {n : ℕ} → ¬ (suc n < zero)
¬s<z = {!!}

_<?_ : ∀ (m n : ℕ) → Dec (m < n)
m <? n = {!!}

-- Some tests.

_ : 2 <? 4 ≡ yes (s<s (s<s (z<s)))
_ = refl

_ : 4 <? 2 ≡ no (¬s<s (¬s<s ¬s<z))
_ = refl

_ : 3 <? 3 ≡ no (¬s<s (¬s<s (¬s<s ¬z<z)))
_ = refl

-- 747/PLFA exercise: DecNatEq (3 points)
-- Decidable equality for natural numbers.

_≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n) -- split m,n
m ≡ℕ? n = {!!}

-- 747/PLFA exercise: ErasBoolDec (3 points)
-- Erasure relates boolean and decidable operations.

∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
∧-× da db = {!!}

∨-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
∨-× da db = {!!}

not-¬ : ∀ {A : Set} (x : Dec A) → not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋
not-¬ da = {!!}

-- 747/PLFA exercise: iff-erasure.

_⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
da ⇔-dec db = {!!}

iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋
iff-⇔ da db = {!!}
