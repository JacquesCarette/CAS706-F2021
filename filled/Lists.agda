{-# OPTIONS --allow-unsolved-metas #-}
module Lists where

-- Library

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_; _∘′_) renaming (id to id→)
open import Level using (Level)

open import Isomorphism using (_≃_; _≲_; _⇔_)

-- Polymorphic lists (parameterized version).

data List (A : Set) : Set where
  []  : List A               -- sometimes called 'nil'
  _∷_ : A → List A → List A  -- sometimes called 'cons' \ : :

infixr 5 _∷_

-- An example.

_ : List ℕ
_ = 0 ∷ 1 ∷ 2 ∷ []

-- An equivalent indexed version

data List′ : Set → Set where
  []′  : ∀ {A : Set} → List′ A
  _∷′_ : ∀ {A : Set} → A → List′ A → List′ A

-- Putting the implicit arguments into our example (but why?).

_ : List ℕ
_ = _∷_ {ℕ} 0 (_∷_ {ℕ} 1 (_∷_ {ℕ} 2 ([] {ℕ})))

-- This pragma would tell Agda to use Haskell lists internally.
-- {-# BUILTIN LIST List #-}

-- Some useful syntax to let us write short lists quickly.

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

infixr 5 _++_

-- Append for lists.

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

_ : [ 0 , 2 , 4 ] ++ [ 3 , 5 ] ≡ [ 0 , 2 , 4 , 3 , 5 ]
_ = refl

-- Associativity of append.
-- Equational reasoning proof in PLFA.

++-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs rewrite ++-assoc xs ys zs = refl

-- Left and right identity for append.

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs = refl

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) rewrite ++-identityʳ xs = refl

-- note how the proofs are 'identical' to the same properties as for ℕ
-- reason: List ⊤ ≃ ℕ

-- Length of a list.

length : ∀ {A : Set} → List A → ℕ
length [] = zero
length (_ ∷ xs) = suc (length xs)

_ : length [ 0 , 1 , 2 ] ≡ 3
_ = refl

-- Reasoning about length.

length-++ : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
length-++ []       ys                         = refl
length-++ (x ∷ xs) ys rewrite length-++ xs ys = refl

-- Reverse using structural recursion (inefficient).

reverse : ∀ {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

_ : reverse [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ = refl

-- Towards more efficient reverse (linear time vs quadratic)
-- Shunt is a generalization of reverse.

shunt : ∀ {A : Set} → List A → List A → List A
shunt []       ys = ys
shunt (x ∷ xs) ys = shunt xs (x ∷ ys)

-- A good explanation of what shunt is doing.

shunt-reverse : ∀ {A : Set} (xs ys : List A) → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys = refl
shunt-reverse (x ∷ xs) ys = begin
  shunt xs (x ∷ ys)           ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
  reverse xs ++ ([ x ] ++ ys) ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
  (reverse xs ++ [ x ]) ++ ys ≡⟨⟩
  (reverse (x ∷ xs) ++ ys)    ∎

-- Now it's clear that more efficient reverse is a special case of shunt.

reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []

-- Confirmation that the two functions are equivalent.

reverses : ∀ {A : Set} (xs : List A) → reverse′ xs ≡ reverse xs
reverses []       = refl
reverses (x ∷ xs) = shunt-reverse xs [ x ]

-- Some common higher-order list functions.

-- 'map' applies a function to every element of a list.

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

_ : map suc [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ = refl

-- An example of using map.

sucs : List ℕ → List ℕ
sucs = map suc

_ : sucs [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ = refl

-- Fold-right: put operator ⊗ between each list element (and supplied final element).
--             ⊗ is considered right-associative.
-- Fold-right is universal for structural recursion on one argument.

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e [] = e
foldr _⊗_ e (x ∷ xs) = x ⊗ foldr _⊗_ e xs

_ : foldr _+_ 0 [ 1 , 2 , 3 , 4 ] ≡ 10
_ = refl

foldr′ : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr′ f e [] = e
foldr′ f e (x ∷ xs) = f x (foldr′ f e xs)

-- Summing a list using foldr.

sum : List ℕ → ℕ
sum = foldr _+_ 0

_ : sum [ 1 , 2 , 3 , 4 ] ≡ 10
_ = refl

prod : List ℕ → ℕ
prod = foldr _*_ 1


-- PLFA exercise: the downFrom function computes a countdown list
-- Prove an equality about its sum

downFrom : ℕ → List ℕ
downFrom zero     =  []
downFrom (suc n)  =  n ∷ downFrom n
_ : downFrom 3 ≡ [ 2 , 1 , 0 ]
_ = refl

-- 'Monoid' is a mathematical term for a set with an associative operator
-- and an element which is the left and right identity (eg lists).

record IsMonoid (A : Set) : Set where
  constructor mon
  field
    id : A
    _⊗_ : A → A → A
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → id ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ id ≡ x

-- The following open command is different from PLFA; it uses instance arguments,
-- which work like typeclasses in Haskell (allow overloading, which is cleaner).

open IsMonoid {{ ...}} public

-- These pragmas make displays of goal and context look nicer.

{-# DISPLAY IsMonoid.id _ = id #-}
{-# DISPLAY IsMonoid._⊗_ _ = _⊗_ #-}

-- We can now describe instances of Monoid using the following notation.

instance

 -- by refinement of the goal
 +-monoid : IsMonoid ℕ
 +-monoid = mon 0 _+_ +-assoc +-identityˡ +-identityʳ

 -- by splitting on the (empty) goal
 *-monoid : IsMonoid ℕ
 IsMonoid.id        *-monoid = 1
 IsMonoid._⊗_       *-monoid = _*_
 IsMonoid.assoc     *-monoid = *-assoc
 IsMonoid.identityˡ *-monoid = *-identityˡ
 IsMonoid.identityʳ *-monoid = *-identityʳ

 ++-monoid : ∀ {A : Set} → IsMonoid (List A)
 ++-monoid = mon [] _++_ ++-assoc ++-identityˡ ++-identityʳ

 -- η for the win!
 →-monoid : ∀ {A : Set} → IsMonoid (A → A)
 →-monoid = mon id→ _∘′_ (λ _ _ _ → refl) (λ _ → refl) λ _ → refl

-- A property of foldr over a monoid.

foldr-monoid : ∀ {A : Set} → {{m : IsMonoid A}} →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ (foldr _⊗_ id xs) ⊗ y
foldr-monoid [] y = sym (identityˡ y)
foldr-monoid (x ∷ xs) y rewrite foldr-monoid xs y | assoc x (foldr _⊗_ id xs) y = refl

-- How foldr commutes with ++ over a monoid.

foldr-monoid-++ : ∀ {A : Set} → {{m : IsMonoid A}} →
  ∀ (xs ys : List A) → foldr _⊗_ id (xs ++ ys) ≡ foldr _⊗_ id xs ⊗ foldr _⊗_ id ys
foldr-monoid-++ [] ys = sym (identityˡ _)
foldr-monoid-++ (x ∷ xs) ys rewrite foldr-monoid-++ xs ys = sym (assoc x _ _)

-- Inductively-defined predicates over lists

-- All P xs means P x holds for every element of xs

data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

_ : All (_≤ 2) [ 0 , 1 , 2 ]
_ = z≤n ∷ s≤s z≤n ∷ s≤s (s≤s z≤n) ∷ []

-- Any P xs means P x holds for some element of xs
-- For Some.
-- Needs to know exactly _where_
data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)
infix 4 _∈_ _∉_

_ : Any ( _≡ 3) [ 4 , 3 , 3 ]
_ = there (there (here refl))

-- membership in list as application of Any

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = here refl

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = there (there (here refl))

not-in : 3 ∉ [ 0 , 1 , 0 , 2 ]
not-in (there (there (there (here ()))))
not-in (there (there (there (there ()))))

-- The development in PLFA, repeated with our notation.

-- refine first to get Isomorphism.equiv
-- As each part is 'complex' and needs splitting on xs, put them in a 'where' clause
All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ {A} {P} xs ys = Isomorphism.equiv
  (split xs ys)
  (join xs ys)
  where
    -- split
    -- to get things to reduce, split on xs
    -- for the second case, also split on the All
    -- we need to be able to re-assemble the results of splitting, so
    -- bind that to a name. Could have used 'case_of_' too (from Function)
    split : (xs ys : List A) → All P (xs ++ ys) → All P xs × All P ys
    split [] ys a = ⟨ [] , a ⟩
    split (x ∷ xs) ys (x₁ ∷ a) =
      let z = split xs ys a in
      ⟨ x₁ ∷ proj₁ z , proj₂ z ⟩
    -- split on xs and on All in both cases, then recurse and reassemble
    join : (xs ys : List A) → All P xs × All P ys → All P (xs ++ ys)
    join [] ys ⟨ Allx , Ally ⟩ = Ally
    join (x ∷ xs) ys ⟨ x₁ ∷ Allx , Ally ⟩ = x₁ ∷ join xs ys ⟨ Allx , Ally ⟩

-- Decidability of All

-- A Boolean analogue of All

all : ∀ {A : Set} → (A → Bool) → List A → Bool
all p  =  foldr _∧_ true ∘ map p

-- A Dec analogue of All

-- A definition of a predicate being decidable

Decidable : ∀ {A : Set} → (A → Set) → Set
Decidable {A} P  =  ∀ (x : A) → Dec (P x)

-- Split on the All first, then ask if P? holds and if it holds for the tail too
-- Depending on those answers gives what case we're in
All? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (All P)
All? P? [] = yes []
All? P? (x ∷ xs) with P? x | All? P? xs
All? P? (x ∷ xs) | yes p | yes p₁ = yes (p ∷ p₁)
All? P? (x ∷ xs) | yes p | no ¬p = no (λ { (x ∷ x₁) → ¬p x₁})
All? P? (x ∷ xs) | no ¬p | _ = no (λ { (x ∷ x₁) → ¬p x})
