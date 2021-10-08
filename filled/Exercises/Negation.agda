module Exercises.Negation where

-- Library

open import Relation.Binary.PropositionalEquality using (_≡_; refl) -- added last
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂)

open import Isomorphism using (extensionality)
open import Relations
open import Negation

-- 747/PLFA exercise: NotFourLTThree (1 point)
-- Show ¬ (4 < 3).

¬4<3 : ¬ (4 < 3)
¬4<3 = {!!}

-- 747/PLFA exercise: LTIrrefl (1 point)
-- < is irreflexive (never reflexive).

¬n<n : ∀ (n : ℕ) → ¬ (n < n)
¬n<n n = {!!}

-- How do we know this does not give a contradiction?
-- The following theorem of intuitionistic logic demonstrates this.
-- (The proof is compact, but takes some thought.)

-- 706: BONUS
em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable = {!!}
