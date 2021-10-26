{-# OPTIONS --allow-unsolved-metas #-}
module Lambda where

-- Library
open import Data.Bool using (T; not)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Isomorphism using (_≲_)  -- \ < ~ (tilde)

-- Identifiers are strings (for familiarity; later, a better choice).

Id : Set
Id = String

-- Precedence and associativity for our language syntax.

infix  5  ƛ_⇒_
infix  5  μ_⇒_
infixl 7  _·_
infix  8  `suc_
infix  9  `_

-- Syntax of terms.

data Term : Set where
  `_                      :  Id → Term            -- variable
  ƛ_⇒_                    :  Id → Term → Term     -- lambda (abstraction)
  _·_                     :  Term → Term → Term   -- application
  `zero                   :  Term
  `suc_                   :  Term → Term
  case_[zero⇒_|suc_⇒_]    :  Term → Term → Id → Term → Term -- "if" on Nat
  μ_⇒_                    :  Id → Term → Term     -- fixpoint for recursion

-- Example expressions.

two : Term
two = `suc `suc `zero

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
         case ` "m"
           [zero⇒ ` "n"
           |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]

p′ : ℕ → ℕ → ℕ
p′ = λ m → λ n → case m of λ { 0 → n ; (suc p) → p′ p n }

2+2 : Term
2+2 = plus · two · two

-- Examples using Church numerals.
-- These take "interpretations" of suc and zero
-- and can be used as functions without resorting to case.

twoᶜ : Term
twoᶜ =  ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

-- plusᶜ can be defined without using fixpoint.

plusᶜ : Term
plusᶜ =  ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
         ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")

fourᶜ : Term
fourᶜ = plusᶜ · twoᶜ · twoᶜ

-- These definitions let us avoid some backticks and quotes.
-- very ill-behaved macro. Don't do this at home!
ƛ′_⇒_ : Term → Term → Term
ƛ′ (` x) ⇒ N  =  ƛ x ⇒ N
ƛ′ _ ⇒ _      =  ⊥-elim impossible
  where postulate impossible : ⊥

case′_[zero⇒_|suc_⇒_] : Term → Term → Term → Term → Term
case′ L [zero⇒ M |suc (` x) ⇒ N ]  =  case L [zero⇒ M |suc x ⇒ N ]
case′ _ [zero⇒ _ |suc _ ⇒ _ ]      =  ⊥-elim impossible
  where postulate impossible : ⊥

μ′_⇒_ : Term → Term → Term
μ′ (` x) ⇒ N  =  μ x ⇒ N
μ′ _ ⇒ _      =  ⊥-elim impossible
  where postulate impossible : ⊥

-- An example of the use of the new notation.

plus′ : Term
plus′ = μ′ + ⇒ ƛ′ m ⇒ ƛ′ n ⇒
          case′ m
            [zero⇒ n
            |suc m ⇒ `suc (+ · m · n) ]
  where
  +  =  ` "+"
  m  =  ` "m"
  n  =  ` "n"

-- PLFA exercise: use the new notation to define multiplication.

-- Bound variables, free variables, closed terms, open terms, alpha renaming.

-- Values.

data Value : Term → Set where

  V-ƛ : ∀ {x N}
      ---------------
    → Value (ƛ x ⇒ N)

  V-zero :
      -----------
      Value `zero

  V-suc : ∀ {V}
    → Value V
      --------------
    → Value (`suc V)

-- Substitution is important in defining reduction.
-- Defined here only for closed terms (simpler).

infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _          =  V
... | no  _          =  ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _          =  ƛ x ⇒ N
... | no  _          =  ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ]   =  L [ y := V ] · M [ y := V ]
(`zero) [ y := V ]   =  `zero
(`suc M) [ y := V ]  =  `suc M [ y := V ]
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
... | yes _          =  case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no  _          =  case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _          =  μ x ⇒ N
... | no  _          =  μ x ⇒ N [ y := V ]


-- Some examples of substitution.

_ : (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] ≡  sucᶜ · (sucᶜ · `zero)
_ = refl

_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] ≡  ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
_ = refl

_ : (ƛ "x" ⇒ ` "y") [ "y" := `zero ] ≡ ƛ "x" ⇒ `zero
_ = refl

_ : (ƛ "x" ⇒ ` "x") [ "x" := `zero ] ≡ ƛ "x" ⇒ ` "x"
_ = refl

_ : (ƛ "y" ⇒ ` "y") [ "x" := `zero ] ≡ ƛ "y" ⇒ ` "y"
_ = refl

-- PLFA exercise: eliminate common code in above with a helper function.

-- Single-step reduction (written \em\to).
-- Compatibility rules (descending into subexpressions) written with \xi (ξ).
-- "Computation here" rules written with \beta (β).

infix 4 _—→_

data _—→_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
      -----------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M —→ M′
      -----------------
    → V · M —→ V · M′

  β-ƛ : ∀ {x N V}
    → Value V
      ------------------------------
    → (ƛ x ⇒ N) · V —→ N [ x := V ]

  ξ-suc : ∀ {M M′}
    → M —→ M′
      ------------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {x L L′ M N}
    → L —→ L′
      -----------------------------------------------------------------
    → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]

  β-zero : ∀ {x M N}
      ----------------------------------------
    → case `zero [zero⇒ M |suc x ⇒ N ] —→ M

  β-suc : ∀ {x V M N}
    → Value V
      ---------------------------------------------------
    → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]

  β-μ : ∀ {x M}
      ------------------------------
    → μ x ⇒ M —→ M [ x := μ x ⇒ M ]


-- Arguments reduced to values before beta-reduction (call-by-value).
-- Terms reduced from left to right.
-- Reduction is deterministic (no choice!).
-- You should be able to prove this now, but it's done later, in Properties.

infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

-- Multistep: the reflexive-transitive closure of single-step.
-- (Notation below resembles tabular reasoning for equivalence,
--  but note we are not using transitivity.)
-- Written \em\rr-.

data _—↠_ : Term → Term → Set where
  _∎ : ∀ M
      ---------
    → M —↠ M

  _—→⟨_⟩_ : ∀ L {M N}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

begin_ : ∀ {M N}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N

-- An alternate definition which makes "reflexive-transitive closure" more obvious.

data _—↠′_ : Term → Term → Set where

  step′ : ∀ {M N}
    → M —→ N
      -------
    → M —↠′ N

  refl′ : ∀ {M}
      -------
    → M —↠′ M

  trans′ : ∀ {L M N}
    → L —↠′ M
    → M —↠′ N
      -------
    → L —↠′ N

-- Determinism means we avoid having to worry about confluence.

-- An example of a multistep reduction.
-- (Not generated by hand, as we'll see later.)
-- Agda can fill in the justifications but not the intermediate terms. Why not?
-- We'll see how to get Agda to do that in 747Properties (it's really cool).

_ : twoᶜ · sucᶜ · `zero —↠ `suc `suc `zero
_ =
  begin
    (twoᶜ · sucᶜ) · `zero                     —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero   —→⟨ β-ƛ V-zero ⟩
    sucᶜ · (sucᶜ · `zero)                     —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    sucᶜ · `suc `zero                         —→⟨ β-ƛ (V-suc V-zero) ⟩
    `suc (`suc `zero)                        ∎

-- Two plus two is four.

_ : plus · two · two —↠ `suc `suc `suc `suc `zero
_ =
  begin
    (plus · two) · two                          —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    ((ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n"
                 |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · two) · two                            —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    (ƛ "n" ⇒
      case two [zero⇒ ` "n"
               |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
         · two                                  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    case two [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ]
  —→⟨ β-suc (V-suc V-zero) ⟩
    `suc (plus · `suc `zero · two)
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc ((ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · `suc `zero · two)
  —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
    `suc ((ƛ "n" ⇒
      case `suc `zero [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · two)
  —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
    `suc (case `suc `zero [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ])
  —→⟨ ξ-suc (β-suc V-zero) ⟩
    `suc `suc (plus · `zero · two)
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
    `suc `suc ((ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · `zero · two)
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
    `suc `suc ((ƛ "n" ⇒
      case `zero [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · two)
  —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
    `suc `suc (case `zero [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ])
  —→⟨ ξ-suc (ξ-suc β-zero) ⟩
    `suc (`suc (`suc (`suc `zero)))
  ∎

-- A longer example of a multistep reduction.

_ : fourᶜ · sucᶜ · `zero —↠ `suc `suc `suc `suc `zero
_ =
  begin
    (ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ ` "m" · ` "s" · (` "n" · ` "s" · ` "z"))
      · twoᶜ · twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ))) ⟩
    (ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ twoᶜ · ` "s" · (` "n" · ` "s" · ` "z"))
      · twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "s" ⇒ ƛ "z" ⇒ twoᶜ · ` "s" · (twoᶜ · ` "s" · ` "z")) · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ twoᶜ · sucᶜ · (twoᶜ · sucᶜ · ` "z")) · `zero
  —→⟨ β-ƛ V-zero ⟩
    twoᶜ · sucᶜ · (twoᶜ · sucᶜ · `zero)
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (twoᶜ · sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · ((ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (sucᶜ · (sucᶜ · `zero))
  —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ V-zero)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (sucᶜ · (`suc `zero))
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (`suc `suc `zero)
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    sucᶜ · (sucᶜ · `suc `suc `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    sucᶜ · (`suc `suc `suc `zero)
  —→⟨ β-ƛ (V-suc (V-suc (V-suc V-zero))) ⟩
   `suc (`suc (`suc (`suc `zero)))
  ∎

-- Adding types to our language.

-- Syntax of types.

infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type

-- Contexts provide types for free variables.
-- Essentially a list of (name, type) pairs, most recently added to right.

infixl 5  _,_⦂_

data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context

-- The lookup judgment.
-- The constructor names are meant to be evocative
-- but for now think of them as 'here' and 'there'.
-- Important: if a parameter name is reused, the latest one is in scope.

infix  4  _∋_⦂_

data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
      ------------------
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
      ------------------
    → Γ , y ⦂ B ∋ x ⦂ A

-- Providing the string inequality proofs required by S
-- can be annoying, and computed proofs can be lengthy.
-- We use the proof by reflection technique described in chapter Decidable
-- to write a "smart" version of S.

S′ : ∀ {Γ x y A B}
   → {x≢y : False (x ≟ y)}
   → Γ ∋ x ⦂ A
     ------------------
   → Γ , y ⦂ B ∋ x ⦂ A

S′ {x≢y = x≢y} x = S (toWitnessFalse x≢y) x

-- The typing judgment. Expressing that a term is well-typed
--   in a certain context.
-- Intro/elim names in comments.

infix  4  _⊢_⦂_

data _⊢_⦂_ : Context → Term → Type → Set where

  -- Axiom
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -------------
    → Γ ⊢ ` x ⦂ A

  -- ⇒-I
  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ⦂ B
      -------------------
    → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B

  -- ⇒-E
  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

  -- ℕ-I₁
  ⊢zero : ∀ {Γ}
      --------------
    → Γ ⊢ `zero ⦂ `ℕ

  -- ℕ-I₂
  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ⦂ `ℕ
      ---------------
    → Γ ⊢ `suc M ⦂ `ℕ

  -- ℕ-E
  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ⦂ `ℕ
    → Γ ⊢ M ⦂ A
    → Γ , x ⦂ `ℕ ⊢ N ⦂ A
      -------------------------------------
    → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ⦂ A

  ⊢μ : ∀ {Γ x M A}
    → Γ , x ⦂ A ⊢ M ⦂ A
      -----------------
    → Γ ⊢ μ x ⇒ M ⦂ A

-- A convenient way of asserting inequality.
-- (Avoids issues with normalizing evidence of negation.)

_≠_ : ∀ (x y : Id) → x ≢ y
x ≠ y  with x ≟ y
...       | no  x≢y  =  x≢y
...       | yes _    =  ⊥-elim impossible
  where postulate impossible : ⊥

-- A typing derivation for the Church numeral twoᶜ.
-- Most of this can be done with refining (why not all?).

Ch : Type → Type
Ch A = (A ⇒ A) ⇒ A ⇒ A

⊢twoᶜ : ∀ {Γ A} → Γ ⊢ twoᶜ ⦂ Ch A
⊢twoᶜ = {!!}

⊢two : ∀ {Γ} → Γ ⊢ two ⦂ `ℕ
⊢two = ?

-- A typing derivation for "two plus two".
-- Done in arbitrary contexts to permit reuse.

⊢plus : ∀ {Γ} → Γ ⊢ plus ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢plus = {!!}

⊢2+2 : ∅ ⊢ plus · two · two ⦂ `ℕ
⊢2+2 = {!!}

⊢plusᶜ : ∀ {Γ A} → Γ  ⊢ plusᶜ ⦂ Ch A ⇒ Ch A ⇒ Ch A
⊢plusᶜ = {!!}

-- The rest of the Church examples.

⊢sucᶜ : ∀ {Γ} → Γ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ
⊢sucᶜ = {!!}

⊢2+2ᶜ : ∅ ⊢ plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero ⦂ `ℕ
⊢2+2ᶜ = {!!}

-- Lookup is injective (a helper for what follows)

∋-injective : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
∋-injective Z        Z          =  refl
∋-injective Z        (S x≢ _)   =  ⊥-elim (x≢ refl)
∋-injective (S x≢ _) Z          =  ⊥-elim (x≢ refl)
∋-injective (S _ ∋x) (S _ ∋x′)  =  ∋-injective ∋x ∋x′

-- Typing is not injective (e.g identity function).

-- Examples of proofs showing that terms are not typable.

nope₁ : ∀ {A} → ¬ (∅ ⊢ `zero · `suc `zero ⦂ A)
nope₁ = {!!}

nope₂ : ∀ {A} → ¬ (∅ ⊢ ƛ "x" ⇒ ` "x" · ` "x" ⦂ A)
nope₂ (⊢ƛ (⊢` ∋x · ⊢` ∋x′))  =  contradiction (∋-injective ∋x ∋x′)
  where
  contradiction : ∀ {A B} → ¬ (A ⇒ B ≡ A)
  contradiction ()

-- Unicode:

{-
⇒  U+21D2  RIGHTWARDS DOUBLE ARROW (\=>)
ƛ  U+019B  LATIN SMALL LETTER LAMBDA WITH STROKE (\Gl-)
·  U+00B7  MIDDLE DOT (\cdot)
—  U+2014  EM DASH (\em)
↠  U+21A0  RIGHTWARDS TWO HEADED ARROW (\rr-)
ξ  U+03BE  GREEK SMALL LETTER XI (\Gx or \xi)
β  U+03B2  GREEK SMALL LETTER BETA (\Gb or \beta)
∋  U+220B  CONTAINS AS MEMBER (\ni)
∅  U+2205  EMPTY SET (\0)
⊢  U+22A2  RIGHT TACK (\vdash or \|-)
⦂  U+2982  Z NOTATION TYPE COLON (\:)
😇  U+1F607  SMILING FACE WITH HALO
😈  U+1F608  SMILING FACE WITH HORNS

-}
