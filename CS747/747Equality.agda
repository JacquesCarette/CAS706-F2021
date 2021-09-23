module 747Equality where

-- No imports!

-- The definition of equality.

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
  
infix 4 _≡_

-- Properties of equality.

sym : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → y ≡ x
  
sym x≡y = {!!}

trans : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z

trans x≡y y≡z = {!!}

-- Congruence: applying a function to equal values yields equal values.

cong : ∀ {A B : Set} (f : A → B) {x y : A}
  → x ≡ y
    ---------
  → f x ≡ f y

cong f x≡y = {!!}

-- Congruence with two arguments.

cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
  → u ≡ x
  → v ≡ y
    -------------
  → f u v ≡ f x y

cong₂ f u≡x v≡y = ?

-- Applying two equal functions to a value yields equal values.

cong-app : ∀ {A B : Set} {f g : A → B}
  → f ≡ g
    ---------------------
  → ∀ (x : A) → f x ≡ g x

cong-app f≡g x = ?

-- Equal values have the same properties.

subst : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y
    ---------
  → P x → P y

subst P x≡y px = ?

-- Here is how equational reasoning is set up.

module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
      -----
    → x ≡ y
  begin x≡y  =  x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
      -----
    → x ≡ y
  x ≡⟨⟩ x≡y  =  x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
      -----
    → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z  =  trans x≡y y≡z

  _∎ : ∀ (x : A)
      -----
    → x ≡ x
  x ∎  =  refl

open ≡-Reasoning

-- The example of equational reasoning from PLFA,
-- demonstrating how additional reasoning to support a ≡⟨_⟩ can be used.

trans′ : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z

trans′ {A} {x} {y} {z} x≡y y≡z =
  begin
    x
  ≡⟨ x≡y ⟩
    y
  ≡⟨ y≡z ⟩
    z
  ∎

-- Another example from PLFA.
-- Definitions repeated to avoid imports.

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

-- Postulates to save space.
-- Don't try this at home!

postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m

+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identity m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎

+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

-- PLFA exercise: define tabular reasoning for ≤ and use it to show
-- that addition is monotonic with respect to ≤.

-- An example to use in understanding rewrite.

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

-- This enables 'rewrite' to work with our local definition of equality.

{-# BUILTIN EQUALITY _≡_ #-}

-- A theorem that benefits from rewrite.

even-comm : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)

even-comm m n ev = ?

-- PLFA shows how to prove +-comm using rewrites (which we already did).

-- Rewrite is just syntactic sugar for 'with'
-- (which is itself syntactic sugar for a helper function).

even-comm′ : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
  
-- We set up a 'with' pattern with the LHS of the rewriting equality, and its proof.
-- Then we split on the proof.

even-comm′ m n ev with   m + n  | +-comm m n
... | r1 | r2       = ?

-- In this case, rewrite is not necessary.

even-comm″ : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm″ m n  =  subst even (+-comm m n)

-- The topics below are not needed in subsequent material.

-- Leibniz equality vs Martin-Löf equality.
-- The correspondence can be proved using Agda (or Coq).

-- First Leibniz equality: two things are equal if
-- every property that holds for one also holds for the other.
-- Note the use of Set₁, the first appearance of Agda levels.
-- Set can be thought of as Set₀.

_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y

-- The properties of equality.

refl-≐ : ∀ {A : Set} {x : A}
  → x ≐ x
refl-≐ P Px  =  Px

trans-≐ : ∀ {A : Set} {x y z : A}
  → x ≐ y
  → y ≐ z
    -----
  → x ≐ z
trans-≐ x≐y y≐z P Px  =  y≐z P (x≐y P Px)

sym-≐ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → y ≐ x

sym-≐ {A} {x} {y} x≐y P  =  Qy
  where
    Q : A → Set
    Q z = P z → P x
    Qx : Q x
    Qx = refl-≐ P
    Qy : Q y
    Qy = x≐y Q Qx

-- Now to show the correspondence.

≡-implies-≐ : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → x ≐ y
≡-implies-≐ x≡y P  =  subst P x≡y

≐-implies-≡ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → x ≡ y
≐-implies-≡ {A} {x} {y} x≐y  =  Qy
  where
    Q : A → Set
    Q z = x ≡ z
    Qx : Q x
    Qx = refl
    Qy : Q y
    Qy = x≐y Q Qx

-- The paper cited in PLFA goes further, and demonstrates an isomorphism
-- under certain reasonable assumptions.

-- Universe polymorphism.
-- We might want to write definitions that hold for arbitrary levels.

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

-- lzero and lsuc create levels the way zero and suc create natural numbers.

-- Generalized definitions of equality and its symmetry

data _≡′_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl′ : x ≡′ x

sym′ : ∀ {ℓ : Level} {A : Set ℓ} {x y : A}
  → x ≡′ y
    ------
  → y ≡′ x

sym′ refl′ = refl′

-- Generalized Leibniz equality

_≐′_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)

_≐′_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x → P y

-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
