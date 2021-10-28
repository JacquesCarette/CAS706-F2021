{-# OPTIONS --allow-unsolved-metas #-}
module Properties where

-- Library

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax; Σ)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (¬_; Dec; yes; no; does; proof; _because_; ofʸ; ofⁿ)
open import Agda.Builtin.Bool using (true; false)
open import Function using (_∘_; case_of_)

open import Isomorphism using (_≃_)
open import Lambda

-- Values do not step.

V¬—→ : ∀ {M N} → Value M → ¬ (M —→ N)
V¬—→ (V-suc vm) (ξ-suc M—→N) = V¬—→ vm M—→N

-- Step implies "not a value".

—→¬V : ∀ {M N} → M —→ N → ¬ Value M
—→¬V msn vm = V¬—→ vm msn

-- Evidence of canonical forms for well-typed values.

infix  4 Canonical_⦂_

data Canonical_⦂_ : Term → Type → Set where

  C-ƛ : ∀ {x A N B} → ∅ , x ⦂ A ⊢ N ⦂ B    → Canonical (ƛ x ⇒ N) ⦂ (A ⇒ B)
  C-zero :                                  Canonical `zero ⦂ `ℕ
  C-suc : ∀ {V}     → Canonical V ⦂ `ℕ    → Canonical `suc V ⦂ `ℕ

-- Every closed, well-typed value is canonical.
-- (That is, we got all the cases in the above definition.)

canonical : ∀ {V A} → ∅ ⊢ V ⦂ A → Value V → Canonical V ⦂ A
canonical v:a vv = {!!}

-- If a term is canonical, it is a value.

value : ∀ {M A} → Canonical M ⦂ A → Value M
value cm:a = {!!}

-- If a term is canonical, it is well-typed in the empty context.

typed : ∀ {M A} → Canonical M ⦂ A → ∅ ⊢ M ⦂ A
typed cm:a = {!!}

-- Evidence for the progress theorem.
-- Either a step can be taken, or we're done (at a value).

data Progress (M : Term) : Set where
  step : ∀ {N} → M —→ N    → Progress M
  done :         Value M   → Progress M

-- The progress theorem: a term well-typed in the empty context satisfies Progress.

progress : ∀ {M A} → ∅ ⊢ M ⦂ A → Progress M
progress m:a = {!!}

-- Preservation: types are preserved by reduction.

-- Extension lemma: helper for the renaming lemma that follows.

ext : ∀ {Γ Δ}
  → (∀ {x A}     →         Γ ∋ x ⦂ A →         Δ ∋ x ⦂ A)
    -----------------------------------------------------
  → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)
ext ρ Z           =  Z
ext ρ (S x≢y ∋x)  =  S x≢y (ρ ∋x)

-- Renaming lemma: if context Δ extends Γ,
-- then type judgments using Γ can be done using Δ.

rename : ∀ {Γ Δ} → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
                 → (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ M ⦂ A)
rename ρ (⊢` ∋w)           =  ⊢` (ρ ∋w)
rename ρ (⊢ƛ ⊢N)           =  ⊢ƛ (rename (ext ρ) ⊢N)
rename ρ (⊢L · ⊢M)         =  (rename ρ ⊢L) · (rename ρ ⊢M)
rename ρ ⊢zero             =  ⊢zero
rename ρ (⊢suc ⊢M)         =  ⊢suc (rename ρ ⊢M)
rename ρ (⊢case ⊢L ⊢M ⊢N)  =  ⊢case (rename ρ ⊢L) (rename ρ ⊢M) (rename (ext ρ) ⊢N)
rename ρ (⊢μ ⊢M)           =  ⊢μ (rename (ext ρ) ⊢M)

-- Above is a general lemma which we need in three specific cases.

-- Weaken: a type judgment in the empty context can be weaked to any context.
-- (Can use C-c C-h to ease write the helper function ρ.)

weaken : ∀ {Γ M A} → ∅ ⊢ M ⦂ A → Γ ⊢ M ⦂ A
weaken {Γ} m:a = {!!}

-- Drop: a type judgment in a context with a repeated variable
-- can drop the earlier occurrence.

drop : ∀ {Γ x M A B C} → Γ , x ⦂ A , x ⦂ B ⊢ M ⦂ C → Γ , x ⦂ B ⊢ M ⦂ C
drop {Γ} {x} {M} {A} {B} {C} m:c = {!!}

-- Swap: if the two most recent additions to the context are for
-- different variables, they can be swapped.

swap : ∀ {Γ x y M A B C} → x ≢ y → Γ , y ⦂ B , x ⦂ A ⊢ M ⦂ C → Γ , x ⦂ A , y ⦂ B ⊢ M ⦂ C
swap {Γ} {x} {y} {M} {A} {B} {C} x≢y m:c = {!!}

-- Substitution lemma: substitution preserves types.

subst : ∀ {Γ x N V A B}
  → ∅ ⊢ V ⦂ A
  → Γ , x ⦂ A ⊢ N ⦂ B
    --------------------
  → Γ ⊢ N [ x := V ] ⦂ B

subst {x = x₂} v:a (⊢` {x = .x₂} Z) with x₂ ≟ x₂
... | .true because ofʸ p = weaken v:a
... | .false because ofⁿ ¬p = ⊥-elim (¬p refl)
subst {x = x₂} v:a (⊢` {x = x₁} (S x x₃)) with x₁ ≟ x₂
... | .true because ofʸ p = ⊥-elim (x p)
... | .false because ofⁿ ¬p = ⊢` x₃
subst {x = x₁} v:a (⊢ƛ {x = x} n:b) with x ≟ x₁
... | .true because ofʸ refl = ⊢ƛ (drop n:b)
... | .false because ofⁿ ¬p = ⊢ƛ (subst v:a (swap ¬p n:b))
subst v:a (n:b · n:b₁) = subst v:a n:b · subst v:a n:b₁
subst v:a ⊢zero = ⊢zero
subst v:a (⊢suc n:b) = ⊢suc (subst v:a n:b)
subst {x = x₁} v:a (⊢case {x = x} n:b n:b₁ n:b₂) with x ≟ x₁
... | .true because ofʸ refl = ⊢case (subst v:a n:b) (subst v:a n:b₁) (drop n:b₂)
... | .false because ofⁿ ¬p = ⊢case (subst v:a n:b) (subst v:a n:b₁) (subst v:a (swap ¬p n:b₂))
subst {x = x₁} v:a (⊢μ {x = x} n:b) with x ≟ x₁
... | .true because ofʸ refl = ⊢μ (drop n:b)
... | .false because ofⁿ ¬p = ⊢μ (subst v:a (swap ¬p n:b))

-- PLFA exercise: if you did the refactoring of substitution in Lambda,
-- redo subst to work with that definition.

-- Finally, a step of a well-typed term preserves types.

preserve : ∀ {M N A}
        → ∅ ⊢ M ⦂ A              → M —→ N         → ∅ ⊢ N ⦂ A
preserve (⊢L · ⊢M)               (ξ-·₁ L—→L′)     =  (preserve ⊢L L—→L′) · ⊢M
preserve (⊢L · ⊢M)               (ξ-·₂ VL M—→M′)  =  ⊢L · (preserve ⊢M M—→M′)
preserve ((⊢ƛ ⊢N) · ⊢V)          (β-ƛ VV)         =  subst ⊢V ⊢N
preserve (⊢suc ⊢M)               (ξ-suc M—→M′)    =  ⊢suc (preserve ⊢M M—→M′)
preserve (⊢case ⊢L ⊢M ⊢N)        (ξ-case L—→L′)   =  ⊢case (preserve ⊢L L—→L′) ⊢M ⊢N
preserve (⊢case ⊢zero ⊢M ⊢N)     (β-zero)         =  ⊢M
preserve (⊢case (⊢suc ⊢V) ⊢M ⊢N) (β-suc VV)       =  subst ⊢V ⊢N
preserve (⊢μ ⊢M)                 (β-μ)            =  subst (⊢μ ⊢M) ⊢M


-- Evaluation.
-- We get this easily by iterating progress and preservation.

-- Problem: some computations do not terminate.
-- Agda will not let us write a partial function.

sucμ  =  μ "x" ⇒ `suc (` "x")

_ = begin
    sucμ                —→⟨ β-μ ⟩
    `suc sucμ           —→⟨ ξ-suc β-μ ⟩
    `suc `suc sucμ      —→⟨ ξ-suc (ξ-suc β-μ) ⟩
    `suc `suc `suc sucμ --  ...
                        ∎

-- One solution: supply "gas" (an integer limiting number of steps)

record Gas : Set where
  constructor gas
  field
    amount : ℕ

data Finished (N : Term) : Set where
  done :       Value N    → Finished N
  out-of-gas :              Finished N

data Steps (L : Term) : Set where
  steps : ∀ {N} → L —↠ N → Finished N → Steps L

-- We can now write the evaluator.
eval : ∀ {L A} → Gas → ∅ ⊢ L ⦂ A → Steps L
eval {L} (gas zero) l:a                                                      = steps (L ∎) out-of-gas
eval {L} (gas (suc x)) l:a with progress l:a
eval {L} (gas (suc x)) l:a | step {N} st with eval (gas x) (preserve l:a st)
...                                      | steps st′ fin                     = steps (L —→⟨ st ⟩ st′) fin
eval {L} (gas (suc x)) l:a               | done v                            = steps (L ∎) (done v)

-- A typing judgment for our previous example.

⊢sucμ : ∅ ⊢ μ "x" ⇒ `suc ` "x" ⦂ `ℕ
⊢sucμ = ⊢μ (⊢suc (⊢` ∋x))
  where
  ∋x = Z

-- Running the nonterminating example for three steps.
-- Use C-c C-n, paste in LHS, copy RHS out of result

_ : eval (gas 3) ⊢sucμ ≡
  steps
   (μ "x" ⇒ `suc ` "x"                      —→⟨ β-μ ⟩
    `suc (μ "x" ⇒ `suc ` "x")               —→⟨ ξ-suc β-μ ⟩
    `suc (`suc (μ "x" ⇒ `suc ` "x"))        —→⟨ ξ-suc (ξ-suc β-μ) ⟩
    `suc (`suc (`suc (μ "x" ⇒ `suc ` "x"))) ∎)
   out-of-gas
_ = refl

-- -- Running a terminating example.
-- -- You should compile the file to run this.

-- _ : eval (gas 100) (⊢twoᶜ · ⊢sucᶜ · ⊢zero) ≡
--   steps
--    ((ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
--    · `zero
--    —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
--     (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
--      `zero
--    —→⟨ β-ƛ V-zero ⟩
--     (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · `zero)
--    —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
--     (ƛ "n" ⇒ `suc ` "n") · `suc `zero
--    —→⟨ β-ƛ (V-suc V-zero) ⟩
--     `suc (`suc `zero)
--    ∎)
--    (done (V-suc (V-suc V-zero)))
-- _ = refl

-- -- Running two plus two.

-- _ : eval (gas 100) ⊢2+2 ≡
--   steps
--    ((μ "+" ⇒
--      (ƛ "m" ⇒
--       (ƛ "n" ⇒
--        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--        ])))
--     · `suc (`suc `zero)
--     · `suc (`suc `zero)
--    —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒
--       `suc
--       ((μ "+" ⇒
--         (ƛ "m" ⇒
--          (ƛ "n" ⇒
--           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--           ])))
--        · ` "m"
--        · ` "n")
--       ]))
--     · `suc (`suc `zero)
--     · `suc (`suc `zero)
--    —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
--     (ƛ "n" ⇒
--      case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--      `suc
--      ((μ "+" ⇒
--        (ƛ "m" ⇒
--         (ƛ "n" ⇒
--          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--          ])))
--       · ` "m"
--       · ` "n")
--      ])
--     · `suc (`suc `zero)
--    —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
--     case `suc (`suc `zero) [zero⇒ `suc (`suc `zero) |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--        (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--      · ` "m"
--      · `suc (`suc `zero))
--     ]
--    —→⟨ β-suc (V-suc V-zero) ⟩
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--        (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--      · `suc `zero
--      · `suc (`suc `zero))
--    —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
--     `suc
--     ((ƛ "m" ⇒
--       (ƛ "n" ⇒
--        case ` "m" [zero⇒ ` "n" |suc "m" ⇒
--        `suc
--        ((μ "+" ⇒
--          (ƛ "m" ⇒
--           (ƛ "n" ⇒
--            case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--            ])))
--         · ` "m"
--         · ` "n")
--        ]))
--      · `suc `zero
--      · `suc (`suc `zero))
--    —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
--     `suc
--     ((ƛ "n" ⇒
--       case `suc `zero [zero⇒ ` "n" |suc "m" ⇒
--       `suc
--       ((μ "+" ⇒
--         (ƛ "m" ⇒
--          (ƛ "n" ⇒
--           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--           ])))
--        · ` "m"
--        · ` "n")
--       ])
--      · `suc (`suc `zero))
--    —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
--     `suc
--     case `suc `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--        (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--      · ` "m"
--      · `suc (`suc `zero))
--     ]
--    —→⟨ ξ-suc (β-suc V-zero) ⟩
--     `suc
--     (`suc
--      ((μ "+" ⇒
--        (ƛ "m" ⇒
--         (ƛ "n" ⇒
--          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--          ])))
--       · `zero
--       · `suc (`suc `zero)))
--    —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
--     `suc
--     (`suc
--      ((ƛ "m" ⇒
--        (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒
--         `suc
--         ((μ "+" ⇒
--           (ƛ "m" ⇒
--            (ƛ "n" ⇒
--             case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--             ])))
--          · ` "m"
--          · ` "n")
--         ]))
--       · `zero
--       · `suc (`suc `zero)))
--    —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
--     `suc
--     (`suc
--      ((ƛ "n" ⇒
--        case `zero [zero⇒ ` "n" |suc "m" ⇒
--        `suc
--        ((μ "+" ⇒
--          (ƛ "m" ⇒
--           (ƛ "n" ⇒
--            case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--            ])))
--         · ` "m"
--         · ` "n")
--        ])
--       · `suc (`suc `zero)))
--    —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
--     `suc
--     (`suc
--      case `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒
--      `suc
--      ((μ "+" ⇒
--        (ƛ "m" ⇒
--         (ƛ "n" ⇒
--          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--          ])))
--       · ` "m"
--       · `suc (`suc `zero))
--      ])
--    —→⟨ ξ-suc (ξ-suc β-zero) ⟩
--     `suc (`suc (`suc (`suc `zero)))
--    ∎)
--    (done (V-suc (V-suc (V-suc (V-suc V-zero)))))
-- _ = refl

-- -- Running 2+2 in Church numerals.

-- _ : eval (gas 100) ⊢2+2ᶜ ≡
--   steps
--    ((ƛ "m" ⇒
--      (ƛ "n" ⇒
--       (ƛ "s" ⇒ (ƛ "z" ⇒ ` "m" · ` "s" · (` "n" · ` "s" · ` "z")))))
--     · (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")))
--     · (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")))
--     · (ƛ "n" ⇒ `suc ` "n")
--     · `zero
--    —→⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ))) ⟩
--     (ƛ "n" ⇒
--      (ƛ "s" ⇒
--       (ƛ "z" ⇒
--        (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · ` "s" ·
--        (` "n" · ` "s" · ` "z"))))
--     · (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")))
--     · (ƛ "n" ⇒ `suc ` "n")
--     · `zero
--    —→⟨ ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
--     (ƛ "s" ⇒
--      (ƛ "z" ⇒
--       (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · ` "s" ·
--       ((ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · ` "s" · ` "z")))
--     · (ƛ "n" ⇒ `suc ` "n")
--     · `zero
--    —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
--     (ƛ "z" ⇒
--      (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
--      ·
--      ((ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
--       · ` "z"))
--     · `zero
--    —→⟨ β-ƛ V-zero ⟩
--     (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
--     ·
--     ((ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
--      · `zero)
--    —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
--     (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
--     ((ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
--      · `zero)
--    —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
--     (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
--     ((ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
--      `zero)
--    —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
--     (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
--     ((ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · `zero))
--    —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ V-zero)) ⟩
--     (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
--     ((ƛ "n" ⇒ `suc ` "n") · `suc `zero)
--    —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc V-zero)) ⟩
--     (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
--     `suc (`suc `zero)
--    —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
--     (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · `suc (`suc `zero))
--    —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
--     (ƛ "n" ⇒ `suc ` "n") · `suc (`suc (`suc `zero))
--    —→⟨ β-ƛ (V-suc (V-suc (V-suc V-zero))) ⟩
--     `suc (`suc (`suc (`suc `zero)))
--    ∎)
--    (done (V-suc (V-suc (V-suc (V-suc V-zero)))))
-- _ = refl

-- Well-typed terms don't get stuck.

-- A term is normal (or a normal form) if it cannot reduce.

Normal : Term → Set
Normal M  =  ∀ {N} → ¬ (M —→ N)

-- A stuck term is normal, but not a value.

Stuck : Term → Set
Stuck M  =  Normal M × ¬ Value M

--
eval′ : ∀ {L A} → Gas → ∅ ⊢ L ⦂ A → Maybe Term
eval′ {L} gs trm =
  case (eval gs trm) of
  λ { (steps {N} _ (done _))    → just N
    ; (steps     _  out-of-gas) → nothing
    }

_ : eval′ (gas 100) ⊢2+2 ≡ just (`suc `suc `suc `suc `zero )
_ = refl

-- Reduction is deterministic, proved.

-- Helper lemma (not needed if 'rewrite' used).

cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E)
  {s w : A} {t x : B} {u y : C} {v z : D}
  → s ≡ w → t ≡ x → u ≡ y → v ≡ z → f s t u v ≡ f w x y z
cong₄ f refl refl refl refl = refl

-- PLFA's proof of deterministic reduction.
-- (Can be simplified using 'rewrite', but not much.)

det : ∀ {M M′ M″}
  → (M —→ M′)    → (M —→ M″)        → M′ ≡ M″
det (ξ-·₁ L—→L′)   (ξ-·₁ L—→L″)     =  cong₂ _·_ (det L—→L′ L—→L″) refl
det (ξ-·₁ L—→L′)   (ξ-·₂ VL M—→M″)  =  ⊥-elim (V¬—→ VL L—→L′)
det (ξ-·₁ L—→L′)   (β-ƛ _)          =  ⊥-elim (V¬—→ V-ƛ L—→L′)
det (ξ-·₂ VL _)    (ξ-·₁ L—→L″)     =  ⊥-elim (V¬—→ VL L—→L″)
det (ξ-·₂ _ M—→M′) (ξ-·₂ _ M—→M″)   =  cong₂ _·_ refl (det M—→M′ M—→M″)
det (ξ-·₂ _ M—→M′) (β-ƛ VM)         =  ⊥-elim (V¬—→ VM M—→M′)
det (β-ƛ _)        (ξ-·₁ L—→L″)     =  ⊥-elim (V¬—→ V-ƛ L—→L″)
det (β-ƛ VM)       (ξ-·₂ _ M—→M″)   =  ⊥-elim (V¬—→ VM M—→M″)
det (β-ƛ _)        (β-ƛ _)          =  refl
det (ξ-suc M—→M′)  (ξ-suc M—→M″)    =  cong `suc_ (det M—→M′ M—→M″)
det (ξ-case L—→L′) (ξ-case L—→L″)   =  cong₄ case_[zero⇒_|suc_⇒_]
                                         (det L—→L′ L—→L″) refl refl refl
det (ξ-case L—→L′) β-zero           =  ⊥-elim (V¬—→ V-zero L—→L′)
det (ξ-case L—→L′) (β-suc VL)       =  ⊥-elim (V¬—→ (V-suc VL) L—→L′)
det β-zero         (ξ-case M—→M″)   =  ⊥-elim (V¬—→ V-zero M—→M″)
det β-zero         β-zero           =  refl
det (β-suc VL)     (ξ-case L—→L″)   =  ⊥-elim (V¬—→ (V-suc VL) L—→L″)
det (β-suc _)      (β-suc _)        =  refl
det β-μ            β-μ              =  refl
