{-# OPTIONS --allow-unsolved-metas #-}
module Exercises.CanonicalBitStrings where

-- Library

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app; sym; trans) -- added last
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-suc; +-identityʳ) -- added last

open import Isomorphism using (_≃_)
open import BinArith using (Bin-ℕ; bits; _x0; _x1; dbl; inc)

tob : ℕ → Bin-ℕ
tob zero = bits
tob (suc m) = inc (tob m)

fromb : Bin-ℕ → ℕ
fromb bits = zero
fromb (n x0) = dbl (fromb n)
fromb (n x1) = suc (dbl (fromb n))

dblb : Bin-ℕ → Bin-ℕ
dblb bits = bits
dblb (b x0) = b x0 x0
dblb (b x1) = b x1 x0

-- The reason that we couldn't prove ∀ {n : Bin-ℕ} → tob (fromb n) ≡ n
-- is because of the possibility of leading zeroes in a Bin-ℕ value.
-- 'bits x0 x0 x1' is such a value that gives a counterexample.
-- However, the theorem is true is true for n without leading zeroes.
-- We define a predicate to be able to state this in a theorem.
-- A value of type One n is evidence that n has a leading one.

data One : Bin-ℕ → Set where
  [bitsx1] : One (bits x1)
  _[x0] : ∀ {n : Bin-ℕ} → One n → One (n x0)
  _[x1] : ∀ {n : Bin-ℕ} → One n → One (n x1)

-- Here's a proof that 'bits x1 x0 x0' has a leading one.

_ : One (bits x1 x0 x0)
_ = [bitsx1] [x0] [x0]

-- There is no value of type One (bits x0 x0 x1).
-- But we can't state and prove this yet, because we don't know
-- how to express negation. That comes in the Connectives chapter.

-- A canonical binary representation is either zero or has a leading one.

data Can : Bin-ℕ → Set where
  [zero] : Can bits
  [pos]  : ∀ {n : Bin-ℕ} → One n → Can n

-- Some obvious examples:

_ : Can bits
_ = [zero]

_ : Can (bits x1 x0)
_ = [pos] ([bitsx1] [x0])

-- The Bin-predicates exercise in PLFA Relations gives three properties of canonicity.
-- The first is that the increment of a canonical number is canonical.

-- Most of the work is done in the following lemma.

-- 747/PLFA exercise: IncCanOne (2 points)
-- The increment of a canonical number has a leading one.

one-inc : ∀ {n : Bin-ℕ} → Can n → One (inc n)
one-inc cn = {!!}

-- The first canonicity property is now an easy corollary.

-- 747/PLFA exercise: OneInc (1 point)

can-inc : ∀ {n : Bin-ℕ} → Can n → Can (inc n)
can-inc cn = {!!}

-- The second canonicity property is that converting a unary number
-- to binary produces a canonical number.

-- 747/PLFA exercise: CanToB (1 point)

to-can : ∀ (n : ℕ) → Can (tob n)
to-can n = {!!}

-- The third canonicity property is that converting a canonical number
-- from binary and back to unary produces the same number.

-- This takes more work, and some helper lemmas from 747Induction.
-- You will need to discover which ones.

-- 747/PLFA exercise: OneDblbX0 (1 point)

-- This helper function relates binary double to the x0 constructor,
-- for numbers with a leading one.

dblb-x0 : ∀ {n : Bin-ℕ} → One n → dblb n ≡ n x0
dblb-x0 on = {!!}

-- We can now prove the third property for numbers with a leading one.

-- 747/PLFA exercise: OneToFrom (3 points)

one-to∘from : ∀ {n : Bin-ℕ} → One n → tob (fromb n) ≡ n
one-to∘from on = {!!}

-- The third property is now an easy corollary.

-- 747/PLFA exercise: CanToFrom (1 point)

can-to∘from : ∀ {n : Bin-ℕ} → Can n → tob (fromb n) ≡ n
can-to∘from cn = {!!}

-- 747/PLFA exercise: OneUnique (2 points)
-- Proofs of positivity are unique.

one-unique : ∀ {n : Bin-ℕ} → (x y : One n) → x ≡ y
one-unique x y = {!!}

-- 747/PLFA exercise: CanUnique (1 point)
-- Proofs of canonicity are unique.

can-unique : ∀ {n : Bin-ℕ} → (x y : Can n) → x ≡ y
can-unique x y = {!!}

-- Do we have an isomorphism between ℕ (unary) and canonical binary representations?
-- Can is not a set, but a family of sets, so it doesn't quite fit
-- into our framework for isomorphism.
-- But we can roll all the values into one set which is isomorphic to ℕ.

-- A CanR value wraps up a Bin-ℕ and proof it has a canonical representation.

record CanR : Set where
  constructor mk-CanR
  field
    n : Bin-ℕ
    cpf : Can n

-- We can show that there is an isomorphism between ℕ and CanR.

-- 747/PLFA exercise: Rewrap (1 point)
-- This helper will be useful.

rewrap : ∀ {m n : Bin-ℕ} → (x : Can m) → (y : Can n) → m ≡ n → mk-CanR m x ≡ mk-CanR n y
rewrap = {!!}

-- 747/PLFA exercise: IsoNCanR (2 points)

iso-ℕ-CanR : ℕ ≃ CanR
iso-ℕ-CanR = {!!}

-- Can we get an isomorphism between ℕ and some binary encoding,
-- without the awkwardness of non-canonical values?
-- Yes: we use digits 1 and 2, instead of 0 and 1 (multiplier/base is still 2).
-- This is known as bijective binary numbering.
-- The counting sequence goes <empty>, 1, 2, 11, 12, 21, 22, 111...

data Bij-ℕ : Set where
  bits : Bij-ℕ
  _x1 : Bij-ℕ → Bij-ℕ
  _x2 : Bij-ℕ → Bij-ℕ

-- There is an isomorphism between ℕ and Bij-ℕ.
-- The proof largely follows the outline of what we did above,
-- and is left as an optional exercise.

-- See PLFA for remarks on standard library definitions similar to those here.

-- Unicode introduced in this chapter:

{-

  ∘  U+2218  RING OPERATOR (\o, \circ, \comp)
  λ  U+03BB  GREEK SMALL LETTER LAMBDA (\lambda, \Gl)
  ≃  U+2243  ASYMPTOTICALLY EQUAL TO (\~-)
  ≲  U+2272  LESS-THAN OR EQUIVALENT TO (\<~)
  ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>)

-}
