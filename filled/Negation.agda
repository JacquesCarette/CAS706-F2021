module Negation where

-- Library

open import Relation.Binary.PropositionalEquality using (_≡_; refl) -- added last
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂)

open import Isomorphism using (extensionality)

-- Negation is defined as implying false.

¬_ : Set → Set
¬ A = A → ⊥

-- if both ¬ A and A hold, then ⊥ holds (not surprisingly).

¬-elim : ∀ {A : Set} → ¬ A → A → ⊥
¬-elim ¬a a = ¬a a

infix 3 ¬_

-- Double negation introduction.

¬¬-intro : ∀ {A : Set} → A → ¬ ¬ A
¬¬-intro a = λ f → f a

-- Double negation cannot be eliminated in intuitionistic logic.

-- Triple negation elimination.

¬¬¬-elim : ∀ {A : Set} → ¬ ¬ ¬ A → ¬ A
¬¬¬-elim a‴ a = a‴ (¬¬-intro a)

-- One direction of the contrapositive.

contraposition : ∀ {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition f ¬b a = ¬b (f a)

-- The other direction cannot be proved in intuitionistic logic.

-- not-equal-to.

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ {()}

-- One of the first-order Peano axioms.

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ { ()}


-- Two proofs of ⊥ → ⊥ which look different but are the same
-- (assuming extensionality).

id : ⊥ → ⊥
id x = x -- this one is lazy

id′ : ⊥ → ⊥
id′ () -- this one is eager

id≡id′ : id ≡ id′
id≡id′ = extensionality (λ())

-- Assuming extensionality, any two proofs of a negation are the same

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality λ x → ⊥-elim (¬x x)

-- Definition: a formula is stable if double negation holds for it.

Stable : Set → Set
Stable A = ¬ ¬ A → A

-- PLFA exercise: every negated formula is stable.
-- This is triple negation elimination.

-- PLFA exercise: the conjunction of two stable formulas is stable.
-- This is the version of DeMorgan's Law that is a special case, above.

-- Where negation sits in the standard library.

import Relation.Nullary using (¬_)
import Relation.Nullary.Negation using (contraposition)

-- Unicode used in this chapter:

{-

  ¬  U+00AC  NOT SIGN (\neg)
  ≢  U+2262  NOT IDENTICAL TO (\==n)

-}
