{-# OPTIONS --allow-unsolved-metas #-}
module Exercises.Lists where

-- Library

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)

open import Isomorphism using (_≃_; _≲_; _⇔_)
open import Lists

-- 747/PLFA exercise: RevCommApp (1 point)
-- How reverse commutes with ++.
-- Changed from PLFA to make xs and ys explicit arguments.

reverse-++-commute : ∀ {A : Set} (xs ys : List A)
  → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-commute xs ys = {!!}

-- 747/PLFA exercise: RevInvol (1 point)
-- Reverse is its own inverse.
-- Changed from PLFA to make xs explicit.

reverse-involutive : ∀ {A : Set} (xs : List A)
  → reverse (reverse xs) ≡ xs
reverse-involutive xs = {!!}

-- 747/PLFA exercise: MapCompose (1 point)
-- The map of a composition is the composition of maps.
-- Changed from PLFA: some arguments made explicit, uses pointwise equality.

map-compose : ∀ {A B C : Set} (f : A → B) (g : B → C) (xs : List A)
  → map (g ∘ f) xs ≡ (map g ∘ map f) xs
map-compose f g xs = {!!}

-- 747/PLFA exercise: MapAppendDist (1 point)
-- The map of an append is the append of maps.
-- Changed from PLFA: some arguments made explicit.

map-++-dist : ∀ {A B : Set} (f : A → B) (xs ys : List A)
 →  map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-dist f xs ys = {!!}

-- 747/PLFA exercise: FoldrOverAppend (1 point)
-- Show that foldr over an append can be expressed as
-- foldrs over each list.

foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A) →
  foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ _⊗_ e xs ys = {!!}

-- 747/PLFA exercise: MapIsFoldr (1 point)
-- Show that map can be expressed as a fold.
-- Changed from PLFA: some arguments made explicit, uses pointwise equality.

map-is-foldr : ∀ {A B : Set} (f : A → B) (xs : List A) →
  map f xs ≡ foldr (λ x rs → f x ∷ rs) [] xs
map-is-foldr f xs = {!!}

-- 747/PLFA exercise: Foldl (1 point)
-- Define foldl, which associates left instead of right, e.g.
--   foldr _⊗_ e [ x , y , z ]  =  x ⊗ (y ⊗ (z ⊗ e))
--   foldl _⊗_ e [ x , y , z ]  =  ((e ⊗ x) ⊗ y) ⊗ z

foldl : ∀ {A B : Set} → (B → A → B) → B → List A → B
foldl _⊗_ e xs = {!!}

-- 747/PLFA exercise: FoldrMonFoldl (2 points)
-- Show that foldr and foldl compute the same value on a monoid
-- when the base case is the identity.
-- Hint: write a helper function for when the base case of foldl is an arbitrary value.

foldl-r-mon : ∀ {A : Set} → {{m : IsMonoid A}} →
  ∀ (xs : List A) → foldl _⊗_ id xs ≡ foldr _⊗_ id xs
foldl-r-mon xs = {!!}

-- PLFA exercise: state and prove Any-++-⇔, and use it to demonstrate
-- an equivalence relating ∈ and _++_.

-- PLFA exercise: Show that the equivalence All-++-⇔ can be extended to an isomorphism.
