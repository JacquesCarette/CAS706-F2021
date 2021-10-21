module Exercises.Lambda where

-- Library
open import Data.Bool using (T; not)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Isomorphism using (_≲_)  -- \ < ~ (tilde)
open import Lambda

-- 747/PLFA exercise: NatMul (1 point)
-- Write multiplication for natural numbers.
-- Alas, refinement will not help, and there is no way (yet) to write tests.

mul : Term
mul = {!!}

-- 747/PLFA exercise: ChurchMul (1 point)
-- Write multiplication for Church numbers.
-- Use of plusᶜ is optional! fixpoint is not needed.

mulᶜ : Term
mulᶜ = {!!}

-- PLFA exercise: use the new notation to define multiplication.

-- 747/PLFA exercise: StepEmbedsIntoStepPrime (2 points)
-- Show that the first definition embeds into the second.
-- Why is it not an isomorphism?

ms1≤ms2 : ∀ {M N} → (M —↠ N) ≲ (M —↠′ N)
ms1≤ms2 = {!!}


-- PLFA exercise: write out the reduction sequence showing one plus one is two.

-- 747/PLFA exercise: MulTyped (2 points)
-- Show that your mul above is well-typed.

⊢mul : ∀ {Γ} → Γ ⊢ mul ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢mul = {!!}

-- 747/PLFA exercise: MulCTyped (2 points)
-- Show that your mulᶜ above is well-typed.

⊢mulᶜ : ∀ {Γ A} → Γ  ⊢ mulᶜ ⦂ Ch A ⇒ Ch A ⇒ Ch A
⊢mulᶜ = {!!}

-- Unicode:

{-
⇒  U+21D2  RIGHTWARDS DOUBLE ARROW (\=>)
ƛ  U+019B  LATIN SMALL LETTER LAMBDA WITH STROKE (\Gl-)
·  U+00B7  MIDDLE DOT (\cdot)
—  U+2014  EM DASH (\em)
↠  U+21A0  RIGHTWARDS TWO HEADED ARROW (\rr-)
ξ  U+03BE  GREEK SMALL LETTER XI (\Gx or \xi)
β  U+03B2  GREEK SMALL LETTER BETA (\Gb or \beta)
∋  U+220B  CONTAINS AS MEMBER (\ni)
∅  U+2205  EMPTY SET (\0)
⊢  U+22A2  RIGHT TACK (\vdash or \|-)
⦂  U+2982  Z NOTATION TYPE COLON (\:)
😇  U+1F607  SMILING FACE WITH HALO
😈  U+1F608  SMILING FACE WITH HORNS

-}
