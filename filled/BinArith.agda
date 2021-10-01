module BinArith where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)


-- Binary representation.
-- Modified from PLFA exercise (thanks to David Darais).

data Bin-ℕ : Set where
  bits : Bin-ℕ
  _x0 : Bin-ℕ → Bin-ℕ
  _x1 : Bin-ℕ → Bin-ℕ

-- Our representation of zero is different from PLFA.
-- We use the empty sequence of bits (more consistent).

bin-zero : Bin-ℕ
bin-zero = bits

bin-one : Bin-ℕ
bin-one = bits x1     -- 1 in binary

bin-two : Bin-ℕ
bin-two = bits x1 x0  -- 10 in binary

-- 747 exercise: Increment (1 point)
-- Define increment (add one).

inc : Bin-ℕ → Bin-ℕ
inc bits = bits x1
inc (m x0) = m x1
inc (m x1) = inc m x0

-- An example/test of increment (you should create others).

_ : inc (bits x1 x0 x1 x1) ≡ bits x1 x1 x0 x0
_ = refl

-- 747 exercise: To/From (2 points)
-- Define 'tob' and 'fromb' operations
-- to convert between unary (ℕ) and binary (Bin-ℕ) notation.
-- Hint: avoid addition and multiplication,
-- and instead use the provided dbl (double) function.
-- This will make later proofs easier.
-- I've put 'b' on the end of the operations to
-- avoid a name clash in a later file.
-- It also makes the direction clear when using them.

dbl : ℕ → ℕ
dbl zero = zero
dbl (suc m) = suc (suc (dbl m))

tob : ℕ → Bin-ℕ
tob zero = bits
tob (suc m) = inc (tob m)

fromb : Bin-ℕ → ℕ
fromb bits = zero
fromb (n x0) = dbl (fromb n)
fromb (n x1) = suc (dbl (fromb n))

-- A couple of examples/tests (you should create others).

_ : tob 6 ≡ bits x1 x1 x0
_ = refl

_ : fromb (bits x1 x1 x0) ≡ 6
_ = refl

-- 747 exercise: BinAdd (2 points)
-- Write the addition function for binary notation.
-- Do NOT use 'to' and 'from'. Work with Bin-ℕ as if ℕ did not exist.
-- Hint: use recursion on both m and n.

_bin-+_ : Bin-ℕ → Bin-ℕ → Bin-ℕ
bits bin-+ n = n
(m x0) bin-+ bits = m x0
(m x0) bin-+ (n x0) = (m bin-+ n) x0
(m x0) bin-+ (n x1) = (m bin-+ n) x1
(m x1) bin-+ bits = m x1
(m x1) bin-+ (n x0) = (m bin-+ n) x1
(m x1) bin-+ (n x1) = inc (m bin-+ n) x0

-- Tests can use to/from, or write out binary constants as below.
-- Again: write more tests!

_ : (bits x1 x0) bin-+ (bits x1 x1) ≡ (bits x1 x0 x1)
_ = refl
