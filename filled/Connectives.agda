{-# OPTIONS --allow-unsolved-metas #-}
module Connectives where

-- Library

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)

-- you may import more, as needed
open import Isomorphism using (extensionality; _≃_; _≲_; _⇔_)

-- Logical AND is Cartesian product.

data _×_ (A : Set) (B : Set) : Set where
  ⟨_,_⟩ : (a : A) → (b : B) → A × B

-- Destructors (eliminators) for ×.
proj₁ : ∀ {A B : Set} → A × B → A
proj₁ ⟨ a , b ⟩ = a

proj₂ : ∀ {A B : Set} → A × B → B
proj₂ ⟨ a , b ⟩ = b    -- x × (x vs \ x)

-- An easier (equivalent) construction using records.
record _×′_ (A B : Set) : Set where
  constructor ⟨_,_⟩′
  field
    proj₁′ : A
    proj₂′ : B
open _×′_

-- Eta-equivalence relates constructors and destructors.

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ a , b ⟩ = refl

-- η for records is 'free'!!!
η-×′ : ∀ {A B : Set} (w : A ×′ B) → ⟨ proj₁′ w , proj₂′ w ⟩′ ≡ w
η-×′ _ = refl

-- Bool (Booleans), a type with exactly two members.

infixr 2 _×_
data Bool : Set where
  true  : Bool
  false : Bool

-- A type with three members (useful for examples).

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

-- Bool × Tri has six members.
-- Here is a function counting them.

×-count : Bool × Tri → ℕ
×-count ⟨ true  , aa ⟩  =  1
×-count ⟨ true  , bb ⟩  =  2
×-count ⟨ true  , cc ⟩  =  3
×-count ⟨ false , aa ⟩  =  4
×-count ⟨ false , bb ⟩  =  5
×-count ⟨ false , cc ⟩  =  6

-- Cartesian product is commutative and associative up to isomorphism.

×-comm : ∀ {A B : Set} → A × B ≃ B × A
_≃_.to ×-comm      ⟨ a , b ⟩ = ⟨ b , a ⟩
_≃_.from ×-comm    ⟨ b , a ⟩ = ⟨ a , b ⟩
_≃_.from∘to ×-comm ⟨ a , b ⟩ = refl
_≃_.to∘from ×-comm ⟨ b , a ⟩ = refl

open _≃_

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
to ×-assoc      ⟨ ⟨ a , b ⟩ , c ⟩ = ⟨ a , ⟨ b , c ⟩ ⟩
from ×-assoc    ⟨ a , ⟨ b , c ⟩ ⟩ = ⟨ ⟨ a , b ⟩ , c ⟩
from∘to ×-assoc ⟨ ⟨ a , b ⟩ , c ⟩ = refl
to∘from ×-assoc ⟨ a , ⟨ b , c ⟩ ⟩ = refl

-- Logical True is a type with one member (unit)

data ⊤ : Set where -- usually pronounced "top" \ t o p
  tt : ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

⊤-count : ⊤ → ℕ
⊤-count tt = 1

-- Unit is the left and right identity of product.

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
to ⊤-identityˡ      = proj₂
from ⊤-identityˡ    = λ a → ⟨ tt , a ⟩
from∘to ⊤-identityˡ ⟨ w , a ⟩ = cong (λ z → ⟨ z , a ⟩) (η-⊤ w)
to∘from ⊤-identityˡ = λ _ → refl

⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ = Isomorphism.mk-≃
  proj₁
  (λ a → ⟨ a , tt ⟩)
  (λ { ⟨ a , w ⟩ → cong (λ z → ⟨ a , z ⟩ ) (η-⊤ w) }) -- pattern-matching lambda
  λ _ → refl

-- Logical OR (disjunction) is sum (disjoint union).

data _⊎_ : Set → Set → Set where
  inj₁ : ∀ {A B : Set} → A → A ⊎ B
  inj₂ : ∀ {A B : Set} → B → A ⊎ B

-- One way to eliminate a sum.
case-⊎ : ∀ {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
case-⊎ f _ (inj₁ x) = f x
case-⊎ _ g (inj₂ x) = g x

-- We typically use pattern-matching to eliminate sums.

-- Eta equivalence for sums.

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ x) = refl

-- A generalization.

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ x) = refl

infix 1 _⊎_

-- Bool ⊎ Tri has five members

⊎-count : Bool ⊎ Tri → ℕ
⊎-count (inj₁ true)   =  1
⊎-count (inj₁ false)  =  2
⊎-count (inj₂ aa)     =  3
⊎-count (inj₂ bb)     =  4
⊎-count (inj₂ cc)     =  5

-- Logical False is the empty type ("bottom", "empty").

data ⊥ : Set where
  -- no clauses!

-- Ex falso quodlibet "from falsehood, anything follows".

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) → ((w : ⊥) → ⊥-elim w ≡ h w)
uniq-⊥ h ()

⊥-count : ⊥ → ℕ
⊥-count w = 0

-- Logical implication (if-then) is... the function type constructor!
-- Eliminating an if-then (modus ponens) is function application.

→-elim : ∀ {A B : Set}
  → (A → B)
  → A
    -------
  → B

→-elim L M = L M

-- This works because eta-reduction for → is built in.

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

-- The function space A → B is sometimes called the exponential Bᴬ.
-- Bool → Tri has 3² or 9 members.

→-count : (Bool → Tri) → ℕ
→-count f with f true | f false
...          | aa     | aa      =   1
...          | aa     | bb      =   2
...          | aa     | cc      =   3
...          | bb     | aa      =   4
...          | bb     | bb      =   5
...          | bb     | cc      =   6
...          | cc     | aa      =   7
...          | cc     | bb      =   8
...          | cc     | cc      =   9

-- In math,   (p ^ n) ^ m = p ^ (n * m).
-- For types, (A ^ B) ^ C ≃ A ^ (B × C).

-- In a language where functions take multiple parameters,
-- this is called "currying".

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
to currying      f = λ A×B → f (proj₁ A×B) (proj₂ A×B)
from currying    g = λ a b → g ⟨ a , b ⟩
from∘to currying f = refl
to∘from currying g = extensionality λ x → cong g (η-× x)

-- In math,   p ^ (n + m) = (p ^ n) * (p ^ m).
-- For types, (A ⊎ B → C) ≃ ((A → C) × (B → C)).

→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ {A} {B} {C} = Isomorphism.mk-≃ to′ from′ from∘to′ to∘from′
  where
    to′ :  (A ⊎ B → C) → (A → C) × (B → C)
    to′ f = ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩ -- ⟨ (λ a → f (inj₁ a)) , (λ b → f (inj₂ b)) ⟩
    from′ : (A → C) × (B → C) → A ⊎ B → C
    from′ ⟨ f , g ⟩ = case-⊎ f g
    from∘to′ : (f : A ⊎ B → C) → (from′ ∘ to′) f  ≡ f
    from∘to′ f = extensionality λ { (inj₁ x) → refl
                                  ; (inj₂ x) → refl
                                  }
    to∘from′ : ∀ y → (to′ ∘ from′) y ≡ y
    to∘from′ ⟨ f , g ⟩ = refl

-- In math,   (p * n) ^ m = (p ^ m) * (n ^ m).
-- For types, (A → B × C) ≃ (A → B) × (A → C).

→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× = {!!}

-- More distributive laws.

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ = {!!}

⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× = {!!}

-- Think of a counterexample to show the above isn't an isomorphism.

-- See PLFA for a number of slight differences with the standard library.

-- Unicode introduced in this chapter:

{-

  ×  U+00D7  MULTIPLICATION SIGN (\x)
  ⊎  U+228E  MULTISET UNION (\u+)
  ⊤  U+22A4  DOWN TACK (\top)
  ⊥  U+22A5  UP TACK (\bot)
  η  U+03B7  GREEK SMALL LETTER ETA (\eta)
  ₁  U+2081  SUBSCRIPT ONE (\_1)
  ₂  U+2082  SUBSCRIPT TWO (\_2)
  ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>, \iff, \lr=)

-}
