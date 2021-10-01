{-# OPTIONS --allow-unsolved-metas #-}
module Isomorphism where

-- Library

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app; sym; trans) -- added last
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-suc; +-identityʳ) -- added last

-- Function composition.

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

_∘′_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘′ f = λ x → g (f x)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

-- Another definition of addition.

_+′_ : ℕ → ℕ → ℕ -- split on n instead, get different code
m +′ zero = m
m +′ suc n = suc (m +′ n)

same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m zero = sym (+-identityʳ m)
same-app m (suc n) rewrite +-suc m n | same-app m n = refl

same : _+′_ ≡ _+_  -- this requires extensionality
same = extensionality λ x → extensionality λ y → same-app x y

-- Isomorphism.

infix 0 _≃_ -- typed as \~-
record _≃_ (A B : Set) : Set where
  constructor mk-≃  -- This has been added, not in PLFA
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_

-- Equivalent to the following:

data _≃′_ (A B : Set): Set where
  mk-≃′ : ∀ (to : A → B) →
          ∀ (from : B → A) →
          ∀ (from∘to : (∀ (x : A) → from (to x) ≡ x)) →
          ∀ (to∘from : (∀ (y : B) → to (from y) ≡ y)) →
          A ≃′ B

to′ : ∀ {A B : Set} → (A ≃′ B) → (A → B)
to′ (mk-≃′ f g g∘f f∘g) = f

from′ : ∀ {A B : Set} → (A ≃′ B) → (B → A)
from′ (mk-≃′ f g g∘f f∘g) = g

from∘to′ : ∀ {A B : Set} → (A≃B : A ≃′ B)
                         → (∀ (x : A)
                         → from′ A≃B (to′ A≃B x) ≡ x)
from∘to′ (mk-≃′ f g g∘f f∘g) = g∘f

to∘from′ : ∀ {A B : Set} → (A≃B : A ≃′ B)
                         → (∀ (y : B)
                         → to′ A≃B (from′ A≃B y) ≡ y)
to∘from′ (mk-≃′ f g g∘f f∘g) = f∘g

-- End of equivalent formulation (records are faster!)

-- Properties of isomorphism.

-- Reflexivity.

≃-refl : ∀ {A : Set} → A ≃ A
-- in empty hole, split on result, get copatterns (not in PLFA)
to ≃-refl = λ x → x
from ≃-refl = λ x → x
from∘to ≃-refl = λ x → refl
to∘from ≃-refl = λ _ → refl

-- define id
id : {A : Set} → A → A
id x = x

≃-refl′ : ∀ {A : Set} → A ≃ A
≃-refl′ = mk-≃ id id (λ _ → refl) (λ _ → refl)

-- Symmetry.

≃-sym : ∀ {A B : Set}
  → A ≃ B
    -----
  → B ≃ A

≃-sym (mk-≃ to₁ from₁ from∘to₁ to∘from₁) = mk-≃ from₁ to₁ to∘from₁ from∘to₁

≃-sym′ : ∀ {A B : Set} → A ≃ B → B ≃ A
≃-sym′ A≃B = mk-≃ (from A≃B) (to A≃B) (to∘from A≃B) (from∘to A≃B)

-- Transitivity.

≃-trans : ∀ {A B C : Set}
  → A ≃ B
  → B ≃ C
    -----
  → A ≃ C

≃-trans A≃B B≃C = mk-≃ (to B≃C ∘ to A≃B) (from A≃B ∘ from B≃C)
  (λ x → trans (cong (from A≃B) (from∘to B≃C _)) (from∘to A≃B x))
  λ y → begin
    to B≃C (to A≃B (from A≃B (from B≃C y))) ≡⟨ cong (to B≃C) (to∘from A≃B _) ⟩
    to B≃C (from B≃C y)                     ≡⟨ to∘from B≃C y ⟩
    y ∎

-- Isomorphism is an equivalence relation.
-- We can create syntax for equational reasoning.

module ≃-Reasoning where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set}
    → A ≃ B
      -----
    → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≃ B
    → B ≃ C
      -----
    → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set)
      -----
    → A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning

-- Embedding (weaker than isomorphism)

infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
open _≲_

≲-refl : ∀ {A : Set} → A ≲ A
≲-refl = record { to = id ; from = id ; from∘to = λ _ → refl }

≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans A≲B B≲C = record
  { to = to B≲C ∘ to A≲B
  ; from = from A≲B ∘ from B≲C
  ; from∘to = λ x → trans (cong (from A≲B) (from∘to B≲C _)) (from∘to A≲B x)
  }

≲-antisym : ∀ {A B : Set}
  → (A≲B : A ≲ B)
  → (B≲A : B ≲ A)
  → (to A≲B ≡ from B≲A)
  → (from A≲B ≡ to B≲A)
    -------------------
  → A ≃ B

≲-antisym A≲B B≲A to≡from from≡to = mk-≃ (to A≲B) (from A≲B)
  (from∘to A≲B)
  lemma
  where
    lemma : ∀ y → to A≲B (from A≲B y) ≡ y
    lemma y rewrite to≡from | from≡to = from∘to B≲A y

-- Tabular reasoning for embedding.

module ≲-Reasoning where

  infix  1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix  3 _≲-∎

  ≲-begin_ : ∀ {A B : Set}
    → A ≲ B
      -----
    → A ≲ B
  ≲-begin A≲B = A≲B

  _≲⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≲ B
    → B ≲ C
      -----
    → A ≲ C
  A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

  _≲-∎ : ∀ (A : Set)
      -----
    → A ≲ A
  A ≲-∎ = ≲-refl

open ≲-Reasoning

-- PLFA exercise: Isomorphism implies embedding.

≃-implies-≲ : ∀ {A B : Set}
  → A ≃ B
    -----
  → A ≲ B

≃-implies-≲ a≃b = record { A≃B }
  where module A≃B = _≃_ a≃b

-- PLFA exercise: propositional equivalence (weaker than embedding).

record _⇔_ (A B : Set) : Set where
  constructor equiv
  field
    to   : A → B
    from : B → A
open _⇔_ -- added

-- This is also an equivalence relation.

⇔-refl : ∀ {A : Set}
    -----
  → A ⇔ A

⇔-refl = equiv id id

⇔-sym : ∀ {A B : Set}
  → A ⇔ B
    -----
  → B ⇔ A

⇔-sym A⇔B = equiv (from A⇔B) (to A⇔B)

⇔-trans : ∀ {A B C : Set}
  → A ⇔ B
  → B ⇔ C
    -----
  → A ⇔ C

⇔-trans A⇔B B⇔C = equiv (to B⇔C ∘ to A⇔B) (from A⇔B ∘ from B⇔C)

-- Unicode introduced in this chapter:

{-

  ∘  U+2218  RING OPERATOR (\o, \circ, \comp)
  λ  U+03BB  GREEK SMALL LETTER LAMBDA (\lambda, \Gl)
  ≃  U+2243  ASYMPTOTICALLY EQUAL TO (\~-)
  ≲  U+2272  LESS-THAN OR EQUIVALENT TO (\<~)
  ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>)

-}
