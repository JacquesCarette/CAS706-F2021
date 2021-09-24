module demo where

open import Relation.Binary.PropositionalEquality
open import Data.Nat

data List (A : Set) : Set where
  empty : List A
  add   : A → List A → List A

-- The list 1, 3, 2

ex1 : List ℕ
ex1 = add 1 (add 3 (add 2 empty))

append : {A : Set} → List A → List A → List A
append empty ys = ys
append (add x xs) ys = add x (append xs ys)

-- A test of append

ex2 : append (add 1 (add 5 (add 3 empty)))
             (add 2 (add 4 empty))
      ≡
      (add 1 (add 5 (add 3 (add 2 (add 4 empty)))))
ex2 = refl

append-empty-left : {A : Set} →
  forall (xs : List A) → append empty xs ≡ xs
append-empty-left xs = refl -- refl is short for 'reflexivity' or 'reflexive'

append-empty-right : {A : Set} →
  forall (xs : List A) → append xs empty ≡ xs
append-empty-right empty = refl
append-empty-right (add x xs) = cong (λ z → add x z) (append-empty-right xs)

-- A use of append-empty-right

ex3 : append (add 1 (add 3 (add 2 empty))) empty
      ≡
      (add 1 (add 3 (add 2 empty)))
ex3 = append-empty-right (add 1 (add 3 (add 2 empty)))
