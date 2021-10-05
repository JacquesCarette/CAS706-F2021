{-# OPTIONS --allow-unsolved-metas #-}
module Quantifiers where

-- Library

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s) -- added ≤
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩) -- added proj₂
open import Data.Sum using (_⊎_; inj₁; inj₂ ) -- added inj₁, inj₂
open import Function using (_∘_) -- added

open import Isomorphism

-- Logical forall is, not surpringly, ∀.
-- Forall elimination is also function application.

∀-elim : {A : Set} {P : A → Set} → (L : ∀ (a : A) → P a) → (a′ : A) → P a′
∀-elim L P = L P

-- In fact, A → B is nicer syntax for ∀ (_ : A) → B.

-- Existential quantification can be defined as a pair:
-- a witness and a proof that the witness satisfies the property.

{- one odd way to encode that is to use a 1-argument data type:
data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : a : A) → B a → Σ A B
-}
-- This is equivalent to defining a dependent record type.

record Σ (A : Set) (B : A → Set) : Set where
  constructor ⟨_,_⟩
  field
    proj₁ : A
    proj₂ : B proj₁

-- Some convenient syntax.

Σ-syntax : (A : Set) (B : A → Set) → Set
Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

-- Unfortunately, we can use the RHS syntax in code,
-- but the LHS will show up in displays of goal and context.


-- By convention, the library uses ∃ when the domain of the bound variable is implicit.

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

-- More special syntax.

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

-- Above we saw two ways of constructing an existential.
-- We eliminate an existential with a function that consumes the
-- witness and proof and reaches a conclusion C.

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set} → (∀ x → B x → C) → ∃[ x ] B x → C
∃-elim f ⟨ x , y ⟩ = f x y

-- This is a generalization of currying (from Connectives).
-- currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
_≃_.to      ∀∃-currying f ⟨ x , y ⟩ = f x y
_≃_.from    ∀∃-currying e x y = e ⟨ x , y ⟩
_≃_.from∘to ∀∃-currying f = refl
_≃_.to∘from ∀∃-currying e = extensionality λ { _ → refl}

-- An existential example: revisiting even/odd.
open import Relations using (even; odd; zero; suc)

-- An number is even iff it is double some other number.
-- A number is odd iff is one plus double some other number.
-- Proofs below.

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ zero = ⟨ zero , refl ⟩
even-∃ (suc x) with odd-∃ x
even-∃ (suc x) | ⟨ x₁ , refl ⟩ = ⟨ suc x₁ , refl ⟩
odd-∃ (suc x) with even-∃ x
odd-∃ (suc x) | ⟨ x₁ , refl ⟩ = ⟨ x₁ , refl ⟩

∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨ zero  , refl ⟩ = zero
∃-even ⟨ suc x , refl ⟩ = suc (∃-odd  ⟨ x , refl ⟩)
∃-odd  ⟨ x     , refl ⟩ = suc (∃-even ⟨ x , refl ⟩)
