module Induction706 where

-- Library

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

-- PLFA coverage of identity, associativity, commutativity, distributivity.

-- An example of the associative law for addition, presented using equational reasoning.

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5
  ≡⟨⟩
    7 + 5
  ≡⟨⟩
    12
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    3 + (4 + 5)
  ∎

-- A theorem easy to prove.

+-identityᴸ : ∀ (m : ℕ) → zero + m ≡ m
+-identityᴸ m = refl

-- A first nontrivial theorem.
-- An equational proof is shown in PLFA.
-- Instead we will use 'rewrite'.

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero = refl
+-identityʳ (suc m) rewrite +-identityʳ m = refl  -- type as +-identity\^r4  ʳ

-- and here's the equational version
+-identityʳ″ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ″ zero = refl
+-identityʳ″ (suc m) = begin
  suc (m + 0) ≡⟨ cong suc (+-identityʳ m) ⟩
  suc m       ∎

-- PLFA's proof uses helpers cong and sym imported from the standard library,
-- and a form of equational reasoning that allows more elaborate justification than above.
-- We can use cong in place of rewrite.

+-identityʳ′ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ′ zero = refl
+-identityʳ′ (suc m) = cong suc (+-identityʳ′ m)

-- Associativity of addition.
-- (Done first in PLFA.)

-- (demonstrate C-c C-c return on ∀-headed types too)
-- λ is typed by \ G l . Mnemonic: G is Greek.  μΜ Τ θξ Ξ
+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p = cong suc (+-assoc m n p)

-- A useful lemma about addition.
-- Equational proof shown in PLFA.

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = cong suc (+-suc m n)

-- Commutativity of addition.
-- Equational proof shown in PLFA.

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm zero n = sym (+-identityʳ n)
+-comm (suc m) n = begin
  suc (m + n)   ≡⟨ cong suc (+-comm m n) ⟩
  suc (n + m)   ≡⟨ sym (+-suc n m) ⟩
  n + suc m     ∎

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ zero n rewrite +-identityʳ n = refl
+-comm′ (suc m) n rewrite +-comm′ m n | +-suc n m = refl

+-comm″ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm″ zero n = sym (+-identityʳ n)
+-comm″ (suc m) n = Eq.trans (cong suc (+-comm m n)) (sym (+-suc n m))

-- 747/PLFA exercise: AddSwap (1 point)
-- Please do this without using induction/recursion.

+-swap : ∀ (m n p : ℕ) → (m + n) + p ≡ n + (m + p)
+-swap m n p = {!!}

-- 747/PLFA exercise: AddDistMult (2 points)
-- Show that addition distributes over multiplication.

*-+-rdistrib : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-+-rdistrib m n p = {!!}

-- 747/PLFA exercise: MultAssoc (2 points)
-- Show that multiplication is associative.

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc m n p = {!!}

-- 747/PLFA exercise: MultComm (3 points)
-- Show that multiplication is commutative.
-- As with the addition proof above, helper lemmas will be needed.

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m n = {!!}

-- 747/PLFA exercise: LeftMonusZero (1 point)
-- PLFA asks "Did your proof require induction?"
-- (which should give you an indication of the expected answer).

0∸n≡0 : ∀ (m : ℕ) → zero ∸ m ≡ zero
0∸n≡0 m = {!!}

-- 747/PLFA exercise: MonusAssocish (2 points)
-- Show a form of associativity for monus.

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc m n p = {!!}

-- PLFA exercise (stretch): distributive and associative laws for exponentiation.

-- 747 extended exercise: properties of binary representation.
-- This is based on the PLFA Bin-laws exercise.

-- Copied from 747Naturals.

data Bin-ℕ : Set where
  bits : Bin-ℕ
  _x0 : Bin-ℕ → Bin-ℕ
  _x1 : Bin-ℕ → Bin-ℕ

dbl : ℕ → ℕ
dbl zero = zero
dbl (suc n) = suc (suc (dbl n))

-- Copy your versions of 'inc', 'to', 'from', 'bin-+' over from 747Naturals.
-- You may choose to change them here to make proofs easier.
-- But make sure to test them if you do!

inc : Bin-ℕ → Bin-ℕ
inc m = {!!}

tob : ℕ → Bin-ℕ
tob m = {!!}

fromb : Bin-ℕ → ℕ
fromb m = {!!}

_bin-+_ : Bin-ℕ → Bin-ℕ → Bin-ℕ
m bin-+ n = {!!}

-- 747 exercise: DoubleB (1 point)
-- Write the Bin-ℕ version of dbl, here called dblb.
-- As with the other Bin-ℕ operations, don't use tob/fromb.

dblb : Bin-ℕ → Bin-ℕ
dblb m = {!!}

-- Here are some properties of tob/fromb/inc suggested by PLFA Induction.
-- Please complete the proofs.

-- 747 exercise: FromInc (1 point)

from∘inc : ∀ (m : Bin-ℕ) → fromb (inc m) ≡ suc (fromb m)
from∘inc m = {!!}

-- 747 exercise: FromToB (1 point)

from∘tob : ∀ (m : ℕ) → fromb (tob m) ≡ m
from∘tob m = {!!}

-- 747 exercise: ToFromB (2 points)
-- The property ∀ (m : Bin-ℕ) → tob (fromb m) ≡ m cannot be proved.
-- Can you see why?
-- However, this restriction of it can be proved.

to/from-corr : ∀ (m : Bin-ℕ) (n : ℕ) → m ≡ tob n → fromb m ≡ n
to/from-corr m n m≡tn = {!!}

-- Here are a few more properties for you to prove.

-- 747 exercise: DblBInc (1 point)

dblb∘inc : ∀ (m : Bin-ℕ) → dblb (inc m) ≡ inc (inc (dblb m))
dblb∘inc m = {!!}

-- 747 exercise: ToDbl (1 point)

to∘dbl : ∀ (m : ℕ) → tob (dbl m) ≡ dblb (tob m)
to∘dbl m = {!!}

-- 747 exercise: FromDblB (1 point)

from∘dblb : ∀ (m : Bin-ℕ) → fromb (dblb m) ≡ dbl (fromb m)
from∘dblb m = {!!}

-- 747 exercise: BinPlusLInc (2 points)
-- This helper function translates the second case for unary addition
--  suc m + n = suc (m + n)
-- into the binary setting. It's useful in the next proof.
-- Hint: induction on both m and n is needed.

bin-+-linc : ∀ (m n : Bin-ℕ) → (inc m) bin-+ n ≡ inc (m bin-+ n)
bin-+-linc m n = {!!}

-- 747 exercise: PlusUnaryBinary (2 points)
-- This theorem relates unary and binary addition.

to∘+ : ∀ (m n : ℕ) → tob (m + n) ≡ tob m bin-+ tob n
to∘+ m n = {!!}

-- This ends the extended exercise.


-- The following theorems proved in PLFA can be found in the standard library.

-- import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)

-- Unicode used in this chapter:

{-

    ∀  U+2200  FOR ALL (\forall, \all)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)
    ′  U+2032  PRIME (\')
    ″  U+2033  DOUBLE PRIME (\')
    ‴  U+2034  TRIPLE PRIME (\')
    ⁗  U+2057  QUADRUPLE PRIME (\')

-}
