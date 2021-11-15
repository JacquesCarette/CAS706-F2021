module Inference where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.String using (String; _≟_)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no; does; proof; _because_; ofʸ; ofⁿ)
open import Function using (_∘_)
open import Data.Bool using (true; false)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse; fromWitnessFalse) -- added
import DBDefs as DB

-- Syntax.

infix   4  _∋_⦂_
infix   4  _⊢_↑_
infix   4  _⊢_↓_
infixl  5  _,_⦂_

infixr  7  _⇒_

infix   5  ƛ_⇒_
infix   5  μ_⇒_
infix   6  _↑
infix   6  _↓_
infixl  7  _·_
infix   8  `suc_
infix   9  `_

Id : Set
Id = String

data Type : Set where
  `ℕ    : Type
  _⇒_   : Type → Type → Type

data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context

data Term⁺ : Set
data Term⁻ : Set

data Term⁺ where
  `_                        : Id → Term⁺
  _·_                       : Term⁺ → Term⁻ → Term⁺
  _↓_                       : Term⁻ → Type → Term⁺

data Term⁻ where
  ƛ_⇒_                     : Id → Term⁻ → Term⁻
  `zero                    : Term⁻
  `suc_                    : Term⁻ → Term⁻
  `case_[zero⇒_|suc_⇒_]    : Term⁺ → Term⁻ → Id → Term⁻ → Term⁻
  μ_⇒_                     : Id → Term⁻ → Term⁻
  _↑                       : Term⁺ → Term⁻

-- Examples of terms.

two : Term⁻
two = `suc (`suc `zero)

plus : Term⁺
plus = (μ "p" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
          `case (` "m") [zero⇒ ` "n" ↑
                        |suc "m" ⇒ `suc (` "p" · (` "m" ↑) · (` "n" ↑) ↑) ])
            ↓ (`ℕ ⇒ `ℕ ⇒ `ℕ)

2+2 : Term⁺
2+2 = plus · two · two
Ch : Type
Ch = (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ

twoᶜ : Term⁻
twoᶜ = (ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · (` "z" ↑) ↑) ↑)

plusᶜ : Term⁺
plusᶜ = (ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
           ` "m" · (` "s" ↑) · (` "n" · (` "s" ↑) · (` "z" ↑) ↑) ↑)
             ↓ (Ch ⇒ Ch ⇒ Ch)

sucᶜ : Term⁻
sucᶜ = ƛ "x" ⇒ `suc (` "x" ↑)

2+2ᶜ : Term⁺
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero

-- Lookup judgments.

data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
      --------------------
    → Γ , x ⦂ A ∋ x ⦂ A

  -- The smart constructor, copied from Lambda.

  S : ∀ {Γ x y A B}
    → {x≢y : False (x ≟ y)}
    → Γ ∋ x ⦂ A
      ------------------
    → Γ , y ⦂ B ∋ x ⦂ A

-- Typing judgments.

data _⊢_↑_ : Context → Term⁺ → Type → Set
data _⊢_↓_ : Context → Term⁻ → Type → Set

data _⊢_↑_ where

  ⊢` : ∀ {Γ A x}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ↑ A

  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ↑ A ⇒ B
    → Γ ⊢ M ↓ A
      -------------
    → Γ ⊢ L · M ↑ B

  ⊢↓ : ∀ {Γ M A}
    → Γ ⊢ M ↓ A
      ---------------
    → Γ ⊢ (M ↓ A) ↑ A

data _⊢_↓_ where

  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ↓ B
      -------------------
    → Γ ⊢ ƛ x ⇒ N ↓ A ⇒ B

  ⊢zero : ∀ {Γ}
      --------------
    → Γ ⊢ `zero ↓ `ℕ

  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ↓ `ℕ
      ---------------
    → Γ ⊢ `suc M ↓ `ℕ

  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ↑ `ℕ
    → Γ ⊢ M ↓ A
    → Γ , x ⦂ `ℕ ⊢ N ↓ A
      -------------------------------------
    → Γ ⊢ `case L [zero⇒ M |suc x ⇒ N ] ↓ A

  ⊢μ : ∀ {Γ x N A}
    → Γ , x ⦂ A ⊢ N ↓ A
      -----------------
    → Γ ⊢ μ x ⇒ N ↓ A

  ⊢↑ : ∀ {Γ M A B}
    → Γ ⊢ M ↑ A
    → A ≡ B
      -------------
    → Γ ⊢ (M ↑) ↓ B

-- Helper functions for computation of types,
-- mostly needed in "no" decidability cases.

-- Deciding equality of types (needed for the ⊢↑ rule).

-- Domain and range of equal function types are equal,
-- and `ℕ is not a function type.

dom≡ : ∀ {A A′ B B′} → A ⇒ B ≡ A′ ⇒ B′ → A ≡ A′
dom≡ refl = refl

rng≡ : ∀ {A A′ B B′} → A ⇒ B ≡ A′ ⇒ B′ → B ≡ B′
rng≡ refl = refl

ℕ≢⇒ : ∀ {A B} → `ℕ ≢ A ⇒ B
ℕ≢⇒ ()

_≟Tp_ : (A B : Type) → Dec (A ≡ B)
`ℕ      ≟Tp `ℕ              =  yes refl
`ℕ      ≟Tp (A ⇒ B)         =  no ℕ≢⇒
(A ⇒ B) ≟Tp `ℕ              =  no (ℕ≢⇒ ∘ sym)
(A ⇒ B) ≟Tp (A′ ⇒ B′)
  with A ≟Tp A′ | B ≟Tp B′
...  | no A≢    | _         =  no (A≢ ∘ dom≡)
...  | yes _    | no B≢     =  no (B≢ ∘ rng≡)
...  | yes A≡   | yes B≡    =  yes (cong₂ _⇒_ A≡ B≡)

-- The uniqueness helpers are needed for negative judgments.

-- Lookup judgments are unique.

uniq-∋ : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
uniq-∋ Z Z                 =  refl
uniq-∋ Z (S {x≢y = x≢y} _) =  ⊥-elim (toWitnessFalse x≢y refl)
uniq-∋ (S {x≢y = x≢y} _) Z =  ⊥-elim (toWitnessFalse x≢y refl)
uniq-∋ (S ∋x) (S ∋x′)      =  uniq-∋ ∋x ∋x′

-- A synthesized type is unique.

uniq-↑ : ∀ {Γ M A B} → Γ ⊢ M ↑ A → Γ ⊢ M ↑ B → A ≡ B
uniq-↑ (⊢` ∋x) (⊢` ∋x′)       =  uniq-∋ ∋x ∋x′
uniq-↑ (⊢L · ⊢M) (⊢L′ · ⊢M′)  =  rng≡ (uniq-↑ ⊢L ⊢L′)
uniq-↑ (⊢↓ ⊢M) (⊢↓ ⊢M′)       =  refl

-- Failed lookups still fail if a different binding is added.

ext∋ : ∀ {Γ B x y}
  → x ≢ y
  → ¬ (∃[ A ]( Γ ∋ x ⦂ A ))
    -----------------------------
  → ¬ (∃[ A ]( Γ , y ⦂ B ∋ x ⦂ A ))
ext∋ x≢y _  ⟨ A , Z ⟩       =  x≢y refl
ext∋ _   ¬∃ ⟨ A , S ⊢x ⟩  =  ¬∃ ⟨ A , ⊢x ⟩

-- Decision procedure for lookup judgments.

lookup : ∀ (Γ : Context) (x : Id)
    -----------------------
  → Dec (∃[ A ](Γ ∋ x ⦂ A))
lookup ∅ x                        =  no  (λ ())
lookup (Γ , y ⦂ B) x with x ≟ y
... | yes refl                    =  yes ⟨ B , Z ⟩
... | no x≢y with lookup Γ x
...             | no  ¬∃          =  no  (ext∋ x≢y ¬∃)
...             | yes ⟨ A , ⊢x ⟩   =  yes ⟨ A , S {x≢y = fromWitnessFalse x≢y} ⊢x ⟩

-- Helpers for promoting a failure to type.

¬arg : ∀ {Γ A B L M}
  → Γ ⊢ L ↑ A ⇒ B
  → ¬ Γ ⊢ M ↓ A
    -------------------------
  → ¬ (∃[ B′ ](Γ ⊢ L · M ↑ B′))
¬arg ⊢L ¬⊢M ⟨ B′ , ⊢L′ · ⊢M′ ⟩ rewrite dom≡ (uniq-↑ ⊢L ⊢L′) = ¬⊢M ⊢M′

¬switch : ∀ {Γ M A B}
  → Γ ⊢ M ↑ A
  → A ≢ B
    ---------------
  → ¬ Γ ⊢ (M ↑) ↓ B
¬switch ⊢M A≢B (⊢↑ ⊢M′ A′≡B) rewrite uniq-↑ ⊢M ⊢M′ = A≢B A′≡B

-- Mutually-recursive synthesize and inherit functions.

synthesize : ∀ (Γ : Context) (M : Term⁺)
    -----------------------
  → Dec (∃[ A ](Γ ⊢ M ↑ A))

inherit : ∀ (Γ : Context) (M : Term⁻) (A : Type)
    ---------------
  → Dec (Γ ⊢ M ↓ A)

synthesize Γ (` x) with lookup Γ x
... | no  ¬∃              =  no  (λ{ ⟨ A , ⊢` ∋x ⟩ → ¬∃ ⟨ A , ∋x ⟩ })
... | yes ⟨ A , ∋x ⟩      =  yes ⟨ A , ⊢` ∋x ⟩
synthesize Γ (L · M) with synthesize Γ L
... | no  ¬∃              =  no  (λ{ ⟨ _ , ⊢L  · _  ⟩  →  ¬∃ ⟨ _ , ⊢L ⟩ })
... | yes ⟨ `ℕ ,    ⊢L ⟩  =  no  (λ{ ⟨ _ , ⊢L′ · _  ⟩  →  ℕ≢⇒ (uniq-↑ ⊢L ⊢L′) })
... | yes ⟨ A ⇒ B , ⊢L ⟩ with inherit Γ M A
...    | no  ¬⊢M          =  no  (¬arg ⊢L ¬⊢M)
...    | yes ⊢M           =  yes ⟨ B , ⊢L · ⊢M ⟩
synthesize Γ (M ↓ A) with inherit Γ M A
... | no  ¬⊢M             =  no  (λ{ ⟨ _ , ⊢↓ ⊢M ⟩  →  ¬⊢M ⊢M })
... | yes ⊢M              =  yes ⟨ A , ⊢↓ ⊢M ⟩

inherit Γ (ƛ x ⇒ N) `ℕ      =  no  (λ())
inherit Γ (ƛ x ⇒ N) (A ⇒ B) with inherit (Γ , x ⦂ A) N B
... | no ¬⊢N                =  no  (λ{ (⊢ƛ ⊢N)  →  ¬⊢N ⊢N })
... | yes ⊢N                =  yes (⊢ƛ ⊢N)
inherit Γ `zero `ℕ          =  yes ⊢zero
inherit Γ `zero (A ⇒ B)     =  no  (λ())
inherit Γ (`suc M) `ℕ with inherit Γ M `ℕ
... | no ¬⊢M                =  no  (λ{ (⊢suc ⊢M)  →  ¬⊢M ⊢M })
... | yes ⊢M                =  yes (⊢suc ⊢M)
inherit Γ (`suc M) (A ⇒ B)  =  no  (λ())
inherit Γ (`case L [zero⇒ M |suc x ⇒ N ]) A with synthesize Γ L
... | no ¬∃                 =  no  (λ{ (⊢case ⊢L  _ _) → ¬∃ ⟨ `ℕ , ⊢L ⟩})
... | yes ⟨ _ ⇒ _ , ⊢L ⟩    =  no  (λ{ (⊢case ⊢L′ _ _) → ℕ≢⇒ (uniq-↑ ⊢L′ ⊢L) })
... | yes ⟨ `ℕ ,    ⊢L ⟩ with inherit Γ M A
...    | no ¬⊢M             =  no  (λ{ (⊢case _ ⊢M _) → ¬⊢M ⊢M })
...    | yes ⊢M with inherit (Γ , x ⦂ `ℕ) N A
...       | no ¬⊢N          =  no  (λ{ (⊢case _ _ ⊢N) → ¬⊢N ⊢N })
...       | yes ⊢N          =  yes (⊢case ⊢L ⊢M ⊢N)
inherit Γ (μ x ⇒ N) A with inherit (Γ , x ⦂ A) N A
... | no ¬⊢N                =  no  (λ{ (⊢μ ⊢N) → ¬⊢N ⊢N })
... | yes ⊢N                =  yes (⊢μ ⊢N)
inherit Γ (M ↑) B with synthesize Γ M
... | no  ¬∃                =  no  (λ{ (⊢↑ ⊢M _) → ¬∃ ⟨ _ , ⊢M ⟩ })
... | yes ⟨ A , ⊢M ⟩ with A ≟Tp B
...   | no  A≢B             =  no  (¬switch ⊢M A≢B)
...   | yes A≡B             =  yes (⊢↑ ⊢M A≡B)

-- Computed by evaluating 'synthesize ∅ 2+2' (no editing needed!).

⊢2+2 : ∅ ⊢ 2+2 ↑ `ℕ
⊢2+2 =
  ⊢↓
  (⊢μ
   (⊢ƛ
    (⊢ƛ
     (⊢case (⊢` (S Z)) (⊢↑ (⊢` Z) refl)
      (⊢suc
       (⊢↑ (⊢` (S (S (S Z))) · ⊢↑ (⊢` Z) refl · ⊢↑ (⊢` (S Z)) refl)
        refl))))))
  · ⊢suc (⊢suc ⊢zero)
  · ⊢suc (⊢suc ⊢zero)


-- Check that synthesis is correct (more below).

_ : synthesize ∅ 2+2 ≡ yes ⟨ `ℕ , ⊢2+2 ⟩
_ = refl

-- Example: 2+2 for Church numerals.
-- Computed as above.

⊢2+2ᶜ : ∅ ⊢ 2+2ᶜ ↑ `ℕ
⊢2+2ᶜ =
  ⊢↓
  (⊢ƛ
   (⊢ƛ
    (⊢ƛ
     (⊢ƛ
      (⊢↑
       (⊢` (S (S (S Z))) · ⊢↑ (⊢` (S Z)) refl ·
        ⊢↑ (⊢` (S (S Z)) · ⊢↑ (⊢` (S Z)) refl · ⊢↑ (⊢` Z) refl) refl)
       refl)))))
  ·
  ⊢ƛ (⊢ƛ (⊢↑ (⊢` (S Z) · ⊢↑ (⊢` (S Z) · ⊢↑ (⊢` Z) refl) refl) refl))
  ·
  ⊢ƛ (⊢ƛ (⊢↑ (⊢` (S Z) · ⊢↑ (⊢` (S Z) · ⊢↑ (⊢` Z) refl) refl) refl))
  · ⊢ƛ (⊢suc (⊢↑ (⊢` Z) refl))
  · ⊢zero

_ : synthesize ∅ 2+2ᶜ ≡ yes ⟨ `ℕ , ⊢2+2ᶜ ⟩
_ = refl

-- Testing error cases (important!).

_ : synthesize ∅ ((ƛ "x" ⇒ ` "y" ↑) ↓ (`ℕ ⇒ `ℕ)) ≡ no _
_ = refl

-- Bad argument type.

_ : synthesize ∅ (plus · sucᶜ) ≡ no _
_ = refl

-- Bad function types.

_ : synthesize ∅ (plus · sucᶜ · two) ≡ no _
_ = refl

_ : synthesize ∅ ((two ↓ `ℕ) · two) ≡ no _
_ = refl

_ : synthesize ∅ (twoᶜ ↓ `ℕ) ≡ no _
_ = refl

-- A natural can't have a function type.

_ : synthesize ∅ (`zero ↓ `ℕ ⇒ `ℕ) ≡ no _
_ = refl

_ : synthesize ∅ (two ↓ `ℕ ⇒ `ℕ) ≡ no _
_ = refl

-- Can't hide a bad type.

_ : synthesize ∅ (`suc twoᶜ ↓ `ℕ) ≡ no _
_ = refl

-- Can't case on a function type.

_ : synthesize ∅
      ((`case (twoᶜ ↓ Ch) [zero⇒ `zero |suc "x" ⇒ ` "x" ↑ ] ↓ `ℕ) ) ≡ no _
_ = refl

-- Can't hide a bad type inside case.

_ : synthesize ∅
      ((`case (twoᶜ ↓ `ℕ) [zero⇒ `zero |suc "x" ⇒ ` "x" ↑ ] ↓ `ℕ) ) ≡ no _
_ = refl

-- Mismatch of inherited and synthesized types.

_ : synthesize ∅ (((ƛ "x" ⇒ ` "x" ↑) ↓ `ℕ ⇒ (`ℕ ⇒ `ℕ))) ≡ no _
_ = refl


-- Erasure: Taking the evidence provided by synthesis on a decorated term
-- and producing the corresponding inherently-typed term.

-- Erasing a type.

∥_∥Tp : Type → DB.Type
∥ `ℕ ∥Tp             =  DB.`ℕ
∥ A ⇒ B ∥Tp          =  ∥ A ∥Tp DB.⇒ ∥ B ∥Tp

-- Erasing a context.

∥_∥Cx : Context → DB.Context
∥ ∅ ∥Cx              =  DB.∅
∥ Γ , x ⦂ A ∥Cx      =  ∥ Γ ∥Cx DB., ∥ A ∥Tp

-- Erasing a lookup judgment.

∥_∥∋ : ∀ {Γ x A} → Γ ∋ x ⦂ A → ∥ Γ ∥Cx DB.∋ ∥ A ∥Tp
∥ Z ∥∋               =  DB.Z
∥ S ⊢x ∥∋         =  DB.S ∥ ⊢x ∥∋

-- Mutually-recursive functions to erase typing judgments.

∥_∥⁺ : ∀ {Γ M A} → Γ ⊢ M ↑ A → ∥ Γ ∥Cx DB.⊢ ∥ A ∥Tp
∥_∥⁻ : ∀ {Γ M A} → Γ ⊢ M ↓ A → ∥ Γ ∥Cx DB.⊢ ∥ A ∥Tp

∥ ⊢` ⊢x ∥⁺           =  DB.` ∥ ⊢x ∥∋
∥ ⊢L · ⊢M ∥⁺         =  ∥ ⊢L ∥⁺ DB.· ∥ ⊢M ∥⁻
∥ ⊢↓ ⊢M ∥⁺           =  ∥ ⊢M ∥⁻

∥ ⊢ƛ ⊢N ∥⁻           =  DB.ƛ ∥ ⊢N ∥⁻
∥ ⊢zero ∥⁻           =  DB.`zero
∥ ⊢suc ⊢M ∥⁻         =  DB.`suc ∥ ⊢M ∥⁻
∥ ⊢case ⊢L ⊢M ⊢N ∥⁻  =  DB.case ∥ ⊢L ∥⁺ ∥ ⊢M ∥⁻ ∥ ⊢N ∥⁻
∥ ⊢μ ⊢M ∥⁻           =  DB.μ ∥ ⊢M ∥⁻
∥ ⊢↑ ⊢M refl ∥⁻      =  ∥ ⊢M ∥⁺

-- Tests that erasure works.
-- (It produces the terms we defined in DeBruijn.)

_ : ∥ ⊢2+2 ∥⁺ ≡ DB.2+2
_ = refl

_ : ∥ ⊢2+2ᶜ ∥⁺ ≡ DB.2+2ᶜ
_ = refl

{-
  Unicode used in this chapter:

  ↓  U+2193:  DOWNWARDS ARROW (\d)
  ↑  U+2191:  UPWARDS ARROW (\u)
  ∥  U+2225:  PARALLEL TO (\||)

-}
