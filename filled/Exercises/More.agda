module Exercises.More where

-- Libraries.

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _*_; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)

-- 706 exercise: New language features (15 points)
-- Add the empty type to what is in the file More (copy everything into here first)
-- Add sum types
-- Add the unit type
-- Add the boolean type in the same style as the Nat type; implement and, or and not
-- (The rules can be found in PLFA, and also most textbooks on programming languages,
--  and various online sources)
--
-- Include examples of computations for each new feature.

-- Hint: do these one at a time.
-- For each section in the file, think whether something has to be added, and what.
-- If you add constructors to an inductive datatype, loading the file
-- will helpfully tell you what cases are missing in code using it, and where.

-- Bonus: Implement the List type
