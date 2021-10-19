{-# OPTIONS --allow-unsolved-metas #-}
module Decidable where

-- Library

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym) -- added sym
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Product using (_×_; proj₁) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function using (_∘_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using ()
  renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)

open import Isomorphism using (_⇔_)
open import Relations using (_<_; s<s; z<s)

-- Here are a couple of examples to show how to prove inequalities
-- (or their negations).

2≤4 : 2 ≤ 4
2≤4 = s≤s (s≤s z≤n)

¬4≤2 : ¬ (4 ≤ 2)
¬4≤2 (s≤s (s≤s ()))

-- We can define a Boolean comparison function.

infix 4 _≤ᵇ_

_≤ᵇ_ : ℕ → ℕ → Bool
zero ≤ᵇ n = true
suc m ≤ᵇ zero = false
suc m ≤ᵇ suc n = m ≤ᵇ n

-- PLFA steps through these computations using equational reasoning.

_ : (2 ≤ᵇ 4) ≡ true
_ =  refl

_ : (4 ≤ᵇ 2) ≡ false
_ = refl

-- Relating evidence and computation.

T : Bool → Set
T true   =  ⊤
T false  =  ⊥

T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ true t = refl

≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T refl = tt

≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤ zero n t = z≤n
≤ᵇ→≤ (suc m) (suc n) t = s≤s (≤ᵇ→≤ m n t)

≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
≤→≤ᵇ z≤n = tt
≤→≤ᵇ (s≤s m≤n) = ≤→≤ᵇ m≤n

-- Getting the best of both worlds!

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

-- Helpers for defining _≤?_
-- If you don't use these, the examples below won't normalize.

¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s m>n (s≤s m≤n) = m>n m≤n

-- Decidable ≤.

_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero ≤? n = yes z≤n
suc m ≤? zero = no (¬s≤z {m})
suc m ≤? suc n = suc-≤? m n (m ≤? n) {- with m ≤? n
... | yes x = yes (s≤s x)
... | no x = no (¬s≤s x) -}
  where
    suc-≤? : (a b : ℕ) → Dec (a ≤ b) → Dec (suc a ≤ suc b)
    suc-≤? a b (yes x) = yes (s≤s x)
    suc-≤? a b (no x) = no (¬s≤s x)

_ : 2 ≤? 4 ≡ yes (s≤s (s≤s z≤n))
_ = refl

_ : 4 ≤? 2 ≡ no (¬s≤s (¬s≤s ¬s≤z))
_ = refl

-- We can also evaluate the LHS of these using C-c C-n.

-- Reusing ≤ᵇ and proofs of equivalence with ≤ to decide ≤.
-- This is hard and tricky!!!
_≤?′_ : ∀ (m n : ℕ) → Dec (m ≤ n)
m ≤?′ n with m ≤ᵇ n | ≤ᵇ→≤ m n | ≤→≤ᵇ {m} {n}
... | false | _ | ¬p = no ¬p
... | true  | p | _  = yes (p tt)

-- Erasing Dec down to Bool (or "isYes").

⌊_⌋ : ∀ {A : Set} → Dec A → Bool
⌊ yes _ ⌋ = true
⌊ no _ ⌋ = false

_≤ᵇ′_ : ℕ → ℕ → Bool
m ≤ᵇ′ n  =  ⌊ m ≤? n ⌋

-- If D is Dec A, then T ⌊ D ⌋ is inhabited exactly when A is inhabited.

toWitness : ∀ {A : Set} {D : Dec A} → T ⌊ D ⌋ → A
toWitness {_} {yes x} _ = x

fromWitness : ∀ {A : Set} {D : Dec A} → A → T ⌊ D ⌋
fromWitness {D = yes x} a = tt
fromWitness {D = no x} a = x a

-- Similar ideas when it is the "no" witnesses we want to handle.

isNo : ∀ {A : Set} → Dec A → Bool
isNo (yes _) = false
isNo (no _)  = true

toWitnessFalse : ∀ {A : Set} {D : Dec A} → T (isNo D) → ¬ A
toWitnessFalse {_} {no x} t = x

fromWitnessFalse : ∀ {A : Set} {D : Dec A} → ¬ A → T (isNo D)
fromWitnessFalse {_} {yes x} ¬a = ¬a x
fromWitnessFalse {_} {no x} ¬a = tt

-- Agda standard library definitions for use of these.

True : ∀ {A : Set} → (D : Dec A) → Set
True Q = T ⌊ Q ⌋

False : ∀ {A : Set} → (D : Dec A) → Set
False Q = T (isNo Q)

-- A concrete example.

≤ᵇ′→≤ : ∀ {m n : ℕ} → T (m ≤ᵇ′ n) → m ≤ n
≤ᵇ′→≤  =  toWitness

≤→≤ᵇ′ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ′ n)
≤→≤ᵇ′  =  fromWitness

-- Conclusion: use Decidables instead of Booleans!

-- Logical connectives for Decidables.

infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true ∧ true = true
true ∧ false = false
false ∧ y = false

infixr 6 _×-dec_

_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes a ×-dec yes b = yes ⟨ a , b ⟩
yes a ×-dec no b = no λ { ⟨ _ , y ⟩ → b y }
no a ×-dec db = no (a ∘ proj₁) -- point-free !
   -- no λ p → a (proj₁ p)  -- <-- this is probably the most readable one?
   -- no λ { ⟨ x , _ ⟩ → a x }

infixr 5 _∨_

_∨_ : Bool → Bool → Bool
true ∨ y = true
false ∨ y = y

infixr 5 _⊎-dec_

_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎-dec _     = yes (inj₁ x)
no x  ⊎-dec yes b = yes (inj₂ b)
no ¬a ⊎-dec no ¬b = no  [ ¬a , ¬b ]′ -- less point-free: no (λ x → [ ¬a , ¬b ]′ x)

not : Bool → Bool
not true  = false
not false = true

¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes x) = no (¬¬-intro x)
¬? (no x) = yes x

-- A Boolean version of implication.

_⊃_ : Bool → Bool → Bool
true ⊃ true = true
true ⊃ false = false
false ⊃ y = true

_→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
yes a →-dec yes b = yes λ _ → b
yes a →-dec no ¬b = no λ f → ¬b (f a)
no ¬a →-dec db = yes λ a → ⊥-elim (¬a a) -- other answer: yes (⊥-elim ∘ ¬ a)

_iff_ : Bool → Bool → Bool
true iff true = true
true iff false = false
false iff true = false
false iff false = true

-- Proof by reflection.
-- Or, getting Agda to construct proofs at compile time.

-- A guarded version of monus.

minus : (m n : ℕ) (n≤m : n ≤ m) → ℕ
minus m zero _ = m
minus (suc m) (suc n) (s≤s m≤n) = minus m n m≤n

-- But we have to provide proofs.

_ : minus 5 3 (s≤s (s≤s (s≤s z≤n))) ≡ 2
_ = refl

-- Agda will fill in an implicit record type if it can fill in all fields.
-- Since ⊤ is defined as a record type with no fields...
-- We can get Agda to compute a value of type True (n ≤? m).

_-_ : (m n : ℕ) {n≤m : True (n ≤? m)} → ℕ
_-_ m n {n≤m} = minus m n (toWitness n≤m)

_ : 5 - 3 ≡ 2
_ = refl

{-
_ : 3 - 5 ≡ 0
_ = {!!}
-}

-- We will later use this to get Agda to compute parts of proofs
-- that would be annoying for us to provide.
