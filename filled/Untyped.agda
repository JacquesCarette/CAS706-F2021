-- FIX: Gas, conlen

module Untyped where

-- Library.

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat
 using (ℕ; zero; suc; _+_; _∸_; _<_; _<?_; s≤s; z≤n)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable
 using (map; True; toWitness; fromWitness) -- added last three
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Nullary.Product using (_×-dec_)

-- Differences here:
---- untyped but intrinsically-scoped;
---- call-by-name instead of call-by-value;
---- full normalization (in lambda bodies);
---- non-deterministic reduction;
---- minimal STLC, with other constructs encoded.

-- Syntax.

infix  4  _⊢_
infix  4  _∋_
infixl 5  _,_

infix  6  ƛ_
infix  6  ′_
infixl 7  _·_

-- Types.

data Type : Set where
  ★ : Type

-- PLFA exercise: Show Type ≃ ⊤.
data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

-- PLFA exercise: Show Context ≃ ℕ

-- Lookup judgment (enforces correct scoping).

data _∋_ : Context → Type → Set where
  Z : ∀ {Γ A}             → Γ , A ∋ A
  S_ : ∀ {Γ A B} → Γ ∋ A  → Γ , B ∋ A

-- Typing judgment (really ensures terms are well-scoped).
data _⊢_ : Context → Type → Set where
  `_ : ∀ {Γ A}    → Γ ∋ A         → Γ ⊢ A
  ƛ_  :  ∀ {Γ}    → Γ , ★ ⊢ ★    → Γ ⊢ ★
  _·_ : ∀ {Γ} → Γ ⊢ ★ → Γ ⊢ ★    → Γ ⊢ ★

-- Natural numbers as variables
count : ∀ {Γ} → ℕ → Γ ∋ ★
count {Γ , ★} zero     =  Z
count {Γ , ★} (suc n)  =  S (count n)
count {∅}     _        =  ⊥-elim impossible
  where postulate impossible : ⊥

#_ : ∀ {Γ} → ℕ → Γ ⊢ ★
# n  =  ` count n

-- Examples.

twoᶜ : ∀ {Γ} → Γ ⊢ ★
twoᶜ = {!!}

fourᶜ : ∀ {Γ} → Γ ⊢ ★
fourᶜ = {!!}

plusᶜ : ∀ {Γ} → Γ ⊢ ★
plusᶜ = {!!}

2+2ᶜ : ∅ ⊢ ★
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ

-- Extension lemma, from DeBruijn.
-- A and B will of course just be ✯.

ext : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

-- Renaming lemma from DeBruijn.

rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    ------------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)

-- Extension lemma for simultaneous substitution from DeBruijn.

exts : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    ----------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)

-- Simultaneous substitution from DeBruijn.

subst : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    ------------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ (` k)          =  σ k
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)

subst-zero : ∀ {Γ B} → (Γ ⊢ B) → ∀ {A} → (Γ , B ∋ A) → (Γ ⊢ A)
subst-zero M p = {!!}

-- Single substitution is a special case, as before.

_[_] : ∀ {Γ A B} → Γ , B ⊢ A    → Γ ⊢ B    → Γ ⊢ A
_[_] {Γ} {A} {B} N M = {!!}

-- We are now going to reduce in the body of lambdas, so
-- reduction will apply to open terms.
-- What are the normal forms?
-- Lambdas whose bodies are normal forms, but also...
-- Variables.
-- Applications L · M where L is a variable and M a normal form.
-- Also where L is K · N where K is a variable and N a normal form.
-- Since we can keep going like this, we create a recursive definition
-- for all of these categories, called Neutral.

data Neutral : ∀ {Γ A} → Γ ⊢ A → Set
data Normal  : ∀ {Γ A} → Γ ⊢ A → Set

data Neutral where
  `_  : ∀ {Γ A} (x : Γ ∋ A)                          → Neutral (` x)
  _·_  : ∀ {Γ} {L M : Γ ⊢ ★} → Neutral L → Normal M  → Neutral (L · M)

data Normal where
  ′_ : ∀ {Γ A} {M : Γ ⊢ A} → Neutral M              → Normal M
  ƛ_  : ∀ {Γ} {N : Γ , ★ ⊢ ★} → Normal N           → Normal (ƛ N)

-- Extending the convenience of using nats as vbls to Neutral.

#′_ : ∀ {Γ} (n : ℕ) → Neutral {Γ} (# n)
#′ n  =  ` count n

-- An example of demonstrating a normal form.
_ : Normal (twoᶜ {∅})
_ = ƛ ƛ (′ #′ 1 · (′ #′ 1 · (′ #′ 0)))

-- Defining reduction.

infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

-- This rule is the same as before.
  ξ₁ : ∀ {Γ} {L L′ M : Γ ⊢ ★}  → L —→ L′    → L · M —→ L′ · M

-- This rule has changed (L need no longer be a value).
-- It now can overlap with the previous rule (non-determinism).

  ξ₂ : ∀ {Γ} {L M M′ : Γ ⊢ ★} → M —→ M′    → L · M —→ L · M′

-- This rule has changed (M need no longer be a value).
-- It now can overlap with the previous rule.

  β : ∀ {Γ} {N : Γ , ★ ⊢ ★} {M : Γ ⊢ ★}   → (ƛ N) · M —→ N [ M ]

-- This rule allows reduction in the body of a lambda.

  ζ : ∀ {Γ} {N N′ : Γ , ★ ⊢ ★} → N —→ N′   → ƛ N —→ ƛ N′

-- Reflexive and transitive closure, as before.

infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
  _∎ : ∀ {Γ A} (M : Γ ⊢ A)    → M —↠ M
  _—→⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A} → L —→ M → M —↠ N → L —↠ N

begin_ : ∀ {Γ} {A} {M N : Γ ⊢ A} → M —↠ N → M —↠ N
begin M—↠N = M—↠N

-- An example of a reduction sequence.
_ : 2+2ᶜ —↠ fourᶜ
_ = begin
    plusᶜ · twoᶜ · twoᶜ                                  —→⟨ ξ₁ β ⟩
    (ƛ ƛ ƛ twoᶜ · # 1 · (# 2 · # 1 · # 0)) · twoᶜ        —→⟨ β ⟩
    ƛ ƛ twoᶜ · # 1 · (twoᶜ · # 1 · # 0)                  —→⟨ ζ (ζ (ξ₁ β)) ⟩
    ƛ ƛ ((ƛ # 2 · (# 2 · # 0)) · (twoᶜ · # 1 · # 0))     —→⟨ ζ (ζ β) ⟩
    ƛ ƛ # 1 · (# 1 · (twoᶜ · # 1 · # 0))                 —→⟨ ζ (ζ (ξ₂ (ξ₂ (ξ₁ β)))) ⟩
    ƛ ƛ # 1 · (# 1 · ((ƛ # 2 · (# 2 · # 0)) · # 0))      —→⟨ ζ (ζ (ξ₂ (ξ₂ β))) ⟩
   ƛ (ƛ # 1 · (# 1 · (# 1 · (# 1 · # 0))))               ∎

-- The progress theorem, adapted from before.
-- Now "done" means not "a value", but "in normal form".

data Progress {Γ A} (M : Γ ⊢ A) : Set where
  step : ∀ {N : Γ ⊢ A} → M —→ N    → Progress M
  done : Normal M                  → Progress M

progress : ∀ {Γ A} → (M : Γ ⊢ A) → Progress M
progress (` x)                                 =  done (′ ` x)
progress (ƛ N)  with  progress N
... | step N—→N′                               =  step (ζ N—→N′)
... | done NrmN                                =  done (ƛ NrmN)
progress (` x · M) with progress M
... | step M—→M′                               =  step (ξ₂ M—→M′)
... | done NrmM                                =  done (′ (` x) · NrmM)
progress ((ƛ N) · M)                           =  step β
progress (L@(_ · _) · M) with progress L
... | step L—→L′                               =  step (ξ₁ L—→L′)
... | done (′ NeuL) with progress M
...    | step M—→M′                            =  step (ξ₂ M—→M′)
...    | done NrmM                             =  done (′ NeuL · NrmM)

-- An evaluator from progress, as before.
-- Note that this is deterministic, as in the theorem above,
-- β and ξ₁ are privileged over ξ₂.

record Gas : Set where
  constructor gas
  field
    amount : ℕ

data Finished {Γ A} (N : Γ ⊢ A) : Set where
   done : Normal N    → Finished N
   out-of-gas :         Finished N

data Steps : ∀ {Γ A} → Γ ⊢ A → Set where
  steps : ∀ {Γ A} {L N : Γ ⊢ A} → L —↠ N → Finished N → Steps L

eval : ∀ {Γ A} → Gas → (L : Γ ⊢ A) → Steps L

eval (gas zero)    L                     =  steps (L ∎) out-of-gas
eval (gas (suc m)) L with progress L
... | done NrmL                          =  steps (L ∎) (done NrmL)
... | step {M} L—→M with eval (gas m) M
...    | steps M—↠N fin                  =  steps (L —→⟨ L—→M ⟩ M—↠N) fin

-- An example.
{-
_ : eval (gas 100) 2+2ᶜ ≡
  steps
   ((ƛ
     (ƛ
      (ƛ
       (ƛ
        (` (S (S (S Z)))) · (` (S Z)) ·
        ((` (S (S Z))) · (` (S Z)) · (` Z))))))
    · (ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z))))
    · (ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z))))
   —→⟨ ξ₁ β ⟩
    (ƛ
     (ƛ
      (ƛ
       (ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) · (` (S Z)) ·
       ((` (S (S Z))) · (` (S Z)) · (` Z)))))
    · (ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z))))
   —→⟨ β ⟩
    ƛ
    (ƛ
     (ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) · (` (S Z)) ·
     ((ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) · (` (S Z)) · (` Z)))
   —→⟨ ζ (ζ (ξ₁ β)) ⟩
    ƛ
    (ƛ
     (ƛ (` (S (S Z))) · ((` (S (S Z))) · (` Z))) ·
     ((ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) · (` (S Z)) · (` Z)))
   —→⟨ ζ (ζ β) ⟩
    ƛ
    (ƛ
     (` (S Z)) ·
     ((` (S Z)) ·
      ((ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) · (` (S Z)) · (` Z))))
   —→⟨ ζ (ζ (ξ₂ (ξ₂ (ξ₁ β)))) ⟩
    ƛ
    (ƛ
     (` (S Z)) ·
     ((` (S Z)) ·
      ((ƛ (` (S (S Z))) · ((` (S (S Z))) · (` Z))) · (` Z))))
   —→⟨ ζ (ζ (ξ₂ (ξ₂ β))) ⟩
    ƛ (ƛ (` (S Z)) · ((` (S Z)) · ((` (S Z)) · ((` (S Z)) · (` Z)))))
   ∎)
   (done
    (ƛ
     (ƛ
      (′
       (` (S Z)) ·
       (′ (` (S Z)) · (′ (` (S Z)) · (′ (` (S Z)) · (′ (` Z)))))))))
_ = refl
-}

-- Scott numerals: representing a number by its eliminator (case)
-- zero = λs.λz.z
-- one  = λs.λz.(s zero)
-- two  = λs.λz.(s one)
-- suc  = λn.λs.λz.(s n)

`zero : ∀ {Γ} → (Γ ⊢ ★)
`zero = ƛ ƛ (# 0)

`suc_ : ∀ {Γ} → (Γ ⊢ ★) → (Γ ⊢ ★)
`suc_ M  = (ƛ ƛ ƛ (# 1 · # 2)) · M

case : ∀ {Γ} → (Γ ⊢ ★) → (Γ ⊢ ★) → (Γ , ★ ⊢ ★)  → (Γ ⊢ ★)
case L M N = L · (ƛ N) · M

-- Fixpoint implemented by the Y combinator.
-- μ = λf. (λx.f (x x)) (λx.f (x x)).

μ_ : ∀ {Γ} → (Γ , ★ ⊢ ★) → (Γ ⊢ ★)
μ N  =  (ƛ ((ƛ (# 1 · (# 0 · # 0))) · (ƛ (# 1 · (# 0 · # 0))))) · (ƛ N)

infix 5 μ_

two : ∀ {Γ} → Γ ⊢ ★
two = `suc `suc `zero

four : ∀ {Γ} → Γ ⊢ ★
four = `suc `suc `suc `suc `zero

plus : ∀ {Γ} → Γ ⊢ ★
plus = μ ƛ ƛ (case (# 1) (# 0) (`suc (# 3 · # 0 · # 1)))

2+2 : ∅ ⊢ ★
2+2 = plus · two · two

-- PLFA exercise: confirm that plus · two · two and four
-- normalize to the same term.

-- PLFA exercise: define multiplication, and confirm that
-- two times two is four.

-- PLFA exercise (stretch): encode the other constructs of More.

-- Multi-step reduction is transitive.
—↠-trans : ∀{Γ}{A}{L M N : Γ ⊢ A} → L —↠ M → M —↠ N → L —↠ N
—↠-trans (M ∎) mn = mn
—↠-trans (L —→⟨ r ⟩ lm) mn = L —→⟨ r ⟩ (—↠-trans lm mn)

-- Nice notation for transitivity.
_—↠⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A} → L —↠ M → M —↠ N → L —↠ N
L —↠⟨ L—↠M ⟩ M—↠N = —↠-trans L—↠M M—↠N

-- Multi-step reduction is a congruence.

appL-cong : ∀ {Γ} {L L' M : Γ ⊢ ★} → L —↠ L' → L · M —↠ L' · M
appL-cong {M = M} (L ∎) = L · M ∎
appL-cong {M = M} (L —→⟨ r ⟩ rs) = L · M —→⟨ ξ₁ r ⟩ appL-cong rs

appR-cong : ∀ {Γ} {L M M' : Γ ⊢ ★} → M —↠ M' → L · M —↠ L · M'
appR-cong {L = L} (M ∎) = L · M ∎
appR-cong {L = L} (M —→⟨ r ⟩ rs) = L · M —→⟨ ξ₂ r ⟩ appR-cong rs

abs-cong : ∀ {Γ} {N N' : Γ , ★ ⊢ ★} → N —↠ N' → ƛ N —↠ ƛ N'
abs-cong (M ∎) = ƛ M ∎
abs-cong (L —→⟨ r ⟩ rs) = ƛ L —→⟨ ζ r ⟩ abs-cong rs
