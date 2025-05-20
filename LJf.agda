module LJf where

open import Data.Unit.Base renaming (⊤ to Unit)
open import Data.Empty using () renaming (⊥ to bot)
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Prelude using (List; ∅; _,_; Either; left; right; _∈_)
open import Prop using (Prop; Ctx; Pvar; ⊤; ⊥; _∧_; _∨_; _⟶_; prop-dec-≡; dec-∈)

data Mode : Set where
  R : Mode  -- Reduce
  S : Mode  -- Search

infix 4 _∣_⊢_∙_
record SequentWithCursorAndMode : Set₂ where
  constructor _∣_⊢_∙_
  field
    leftOfCursor  : Ctx
    rightOfCursor : Ctx
    succedent     : Prop
    mode          : Mode
open SequentWithCursorAndMode

infixr 7 _,,_
_,,_ : {A : Set} → A → List A → List A
x ,, xs = xs , x

isPvarOr⊥ : Prop → Set
isPvarOr⊥ (Pvar _) = Unit
isPvarOr⊥ ⊥ = Unit
isPvarOr⊥ _ = bot

infix 3 _∈LJf
data _∈LJf : SequentWithCursorAndMode → Set₂ where
  id-f⟨ : ∀ {Γ Δ} {n} {C}
        → Γ ∣ Pvar n ,, Δ ⊢ C ∙ R ∈LJf
          ------------------- id-f⟨
        → Γ , Pvar n ∣ Δ ⊢ C ∙ R ∈LJf

  id  : ∀ {Γ Δ} {n}
        ----------------------- id
      → Γ , Pvar n ∣ Δ ⊢ Pvar n ∙ R ∈LJf

  ⊤R  : ∀ {Γ}
        --------- ⊤R
      → ∅ ∣ Γ ⊢ ⊤ ∙ R ∈LJf

  ⊤L  : ∀ {Γ Δ} {C}
      → Γ ∣ Δ ⊢ C ∙ R ∈LJf
        ------------- ⊤L
      → Γ , ⊤ ∣ Δ ⊢ C ∙ R ∈LJf

  ⊥L  : ∀ {Γ Δ} {C}
        ------------- ⊥L
      → Γ , ⊥ ∣ Δ ⊢ C ∙ R ∈LJf

  ∧R  : ∀ {Γ} {A B}
      → Γ ∣ ∅ ⊢ A ∙ R ∈LJf
      → Γ ∣ ∅ ⊢ B ∙ R ∈LJf
        -------------- ∧R
      → ∅ ∣ Γ ⊢ A ∧ B ∙ R ∈LJf

  ∧L  : ∀ {Γ Δ} {A B C}
      → Γ , A , B ∣ Δ ⊢ C ∙ R ∈LJf
        ----------------- ∧L
      → Γ , A ∧ B ∣ Δ ⊢ C ∙ R ∈LJf

  ∨R₁ : ∀ {Γ} {A B : Prop}
      → Γ ∣ ∅ ⊢ A ∙ R ∈LJf
        -------------- ∨R₁
      → ∅ ∣ Γ ⊢ A ∨ B ∙ R ∈LJf

  ∨R₂ : ∀ {Γ} {A B : Prop}
      → Γ ∣ ∅ ⊢ B ∙ R ∈LJf
        -------------- ∨R₂
      → ∅ ∣ Γ ⊢ A ∨ B ∙ R ∈LJf

  ∨L  : ∀ {Γ Δ} {A B C : Prop}
      → Γ , A ∣ Δ ⊢ C ∙ R ∈LJf
      → Γ , B ∣ Δ ⊢ C ∙ R ∈LJf
        ------------------ ∨L
      → Γ , A ∨ B ∣ Δ ⊢ C ∙ R ∈LJf

  →R  : ∀ {Γ} {A B : Prop}
      → Γ , A ∣ ∅ ⊢ B ∙ R ∈LJf
        ------------------- →R
      → ∅ ∣ Γ ⊢ A ⟶ B ∙ R ∈LJf

  ⊤→L : ∀ {Γ Δ} {B C : Prop}
      → Γ , B ∣ Δ ⊢ C ∙ R ∈LJf
        ----------------- ⊤→L
      → Γ , ⊤ ⟶ B ∣ Δ ⊢ C ∙ R ∈LJf

  ⊥→L : ∀ {Γ Δ} {B C : Prop}
      → Γ ∣ Δ ⊢ C ∙ R ∈LJf
        ----------------- ⊥→L
      → Γ , ⊥ ⟶ B ∣ Δ ⊢ C ∙ R ∈LJf

  ∧→L : ∀ {Γ Δ} {A₁ A₂ B C : Prop}
      → Γ , A₁ ⟶ (A₂ ⟶ B) ∣ Δ ⊢ C ∙ R ∈LJf
        ------------------------------ ∧→L
      → Γ , (A₁ ∧ A₂) ⟶ B ∣ Δ ⊢ C ∙ R ∈LJf

  ∨→L : ∀ {Γ Δ} {A₁ A₂ B C : Prop}
      → Γ , A₁ ⟶ B , A₂ ⟶ B ∣ Δ ⊢ C ∙ R ∈LJf
        -------------------------------- ∨→L
      → Γ , (A₁ ∨ A₂) ⟶ B ∣ Δ ⊢ C ∙ R ∈LJf

  →→L : ∀ {Γ Δ} {A₁ A₂ B C : Prop}
      → Γ , A₂ ⟶ B , A₁ ∣ Δ ⊢ A₂ ∙ R ∈LJf
      → Γ , B ∣ Δ  ⊢ C ∙ R ∈LJf
        ------------------------- →→L
      → Γ , (A₁ ⟶ A₂) ⟶ B ∣ Δ ⊢ C ∙ R ∈LJf

  P→L : ∀ {Γ Δ} {n} {B C : Prop} {m}
      → Either (Pvar n ∈ Γ) (Pvar n ∈ Δ)
      → Γ , B ∣ Δ ⊢ C ∙ R ∈LJf
        ---------------------- P→L
      → Γ , Pvar n ⟶ B ∣ Δ ⊢ C ∙ m ∈LJf

  P→-f⟨ : ∀ {Γ Δ} {n} {B C}
        → Γ ∣ Pvar n ⟶ B ,, Δ ⊢ C ∙ R ∈LJf
          ---------------------- P→-f⟨
        → Γ , Pvar n ⟶ B ∣ Δ ⊢ C ∙ R ∈LJf

  initSearch : ∀ {Γ} {C}
             → isPvarOr⊥ C
             → Γ ∣ ∅ ⊢ C ∙ S ∈LJf
               ------------------ init
             → ∅ ∣ Γ ⊢ C ∙ R ∈LJf

  continueSearch : ∀ {Γ Δ} {A C}
                 → Γ ∣ A ,, Δ ⊢ C ∙ S ∈LJf
                   ----------------------- cont
                 → Γ , A ∣ Δ ⊢ C ∙ S ∈LJf

derivationFor : SequentWithCursorAndMode → Set₂
derivationFor (Γ ∣ Δ ⊢ C ∙ m) = Γ ∣ Δ ⊢ C ∙ m ∈LJf

{-# TERMINATING #-}
isProvable : (s : SequentWithCursorAndMode)
           → Either (derivationFor s) (¬ derivationFor s)
-- This is the base-case where we fail.
-- The cursor has reached the end in search mode.
isProvable (∅ ∣ _ ⊢ _ ∙ S)        = right λ()

isProvable (∅ ∣ _ ⊢ ⊤ ∙ R)        = left ⊤R

-- If the cursor reaches the end in reduce mode and
-- we cannot reduce the succedent we
-- rewind and change to search mode.
isProvable (∅ ∣ Γ ⊢ ⊥ ∙ R)
 with isProvable (Γ ∣ ∅ ⊢ ⊥ ∙ S)
... | left  𝒟₁ = left (initSearch tt 𝒟₁)
... | right h = right λ{ (initSearch _ 𝒟₁) → h 𝒟₁ }
isProvable (∅ ∣ Γ ⊢ Pvar n ∙ R)
 with isProvable (Γ ∣ ∅ ⊢ Pvar n ∙ S)
... | left  𝒟₁ = left (initSearch tt 𝒟₁)
... | right h = right λ{ (initSearch _ 𝒟₁) → h 𝒟₁ }

-- If the cursor reached the end in reduce mode
-- and we can reduce the succedent then we do that
-- and rewind the cursor
isProvable (∅ ∣ Γ ⊢ (A ∧ B) ∙ R)
  with isProvable (Γ ∣ ∅ ⊢ A ∙ R)
     | isProvable (Γ ∣ ∅ ⊢ B ∙ R)
...  | left  h | left  t = left (∧R h t)
...  | right h | _       = right λ{ (∧R x _) → h x}
...  | _       | right h = right λ{ (∧R _ x) → h x}
isProvable (∅ ∣ Γ ⊢ (A ∨ B) ∙ R)
  with isProvable (Γ ∣ ∅ ⊢ A ∙ R)
     | isProvable (Γ ∣ ∅ ⊢ B ∙ R)
...  | (left  ⊢A) | _          = left (∨R₁ ⊢A)
...  | _          | (left  ⊢B) = left (∨R₂ ⊢B)
...  | (right ⊬A) | (right ⊬B) = right λ{ (∨R₁ ⊢A) → ⊬A ⊢A
                                        ; (∨R₂ ⊢B) → ⊬B ⊢B
                                        }
isProvable (∅ ∣ Γ ⊢ (A ⟶ B) ∙ R)
 with isProvable (Γ , A ∣ ∅ ⊢ B ∙ R)
... | left  h = left (→R h)
... | right h = right λ{ (→R x) → h x }

-- Reduce propositions in the context.
isProvable (Γ , ⊤ ∣ Δ ⊢ C ∙ R)
 with isProvable (Γ ∣ Δ ⊢ C ∙ R)
... | left  h = left (⊤L h)
... | right h = right λ{ (⊤L x) → h x }
isProvable (Γ , ⊥  ∣ _ ⊢ _ ∙ R) = left ⊥L
isProvable (Γ , Pₙ@(Pvar n) ∣ Δ ⊢ C ∙ R)
 with prop-dec-≡ Pₙ C
... | left  refl = left id
... | right Pₙ≢C with isProvable (Γ ∣ Pₙ ,, Δ ⊢ C ∙ R)
...                 | left  x = left (id-f⟨ x)
...                 | right x = right λ{ id → Pₙ≢C refl
                                       ; (id-f⟨ y) → x y
                                       }
isProvable (Γ , A ∧ B ∣ Δ ⊢ C ∙ R)
 with isProvable (Γ , A , B ∣ Δ ⊢ C ∙ R)
... | left  x = left (∧L x )
... | right x = right λ{ (∧L y) → x y }
isProvable (Γ , A ∨ B ∣ Δ ⊢ C ∙ R)
 with isProvable (Γ , A ∣ Δ ⊢ C ∙ R) | isProvable (Γ , B ∣ Δ ⊢ C ∙ R)
... | left  A⊢C | left  B⊢C = left (∨L A⊢C B⊢C)
... | right A⊬C | _         = right λ{ (∨L A⊢C _) → A⊬C A⊢C
                                        }
...    | _         | right B⊬C = right λ{ (∨L _ B⊢C) → B⊬C B⊢C
                                        }
isProvable (Γ , ⊤ ⟶ B ∣ Δ ⊢ C ∙ R)
 with isProvable (Γ , B ∣ Δ ⊢ C ∙ R)
... | left  h = left (⊤→L h)
... | right h = right λ{ (⊤→L x) → h x }
isProvable (Γ , ⊥ ⟶ B ∣ Δ ⊢ C ∙ R)
 with isProvable (Γ ∣ Δ ⊢ C ∙ R)
... | left  h = left (⊥→L h)
... | right h = right λ{ (⊥→L x) → h x }
isProvable (Γ , A₁ ∧ A₂ ⟶ B ∣ Δ ⊢ C ∙ R)
 with isProvable (Γ , A₁ ⟶ (A₂ ⟶ B) ∣ Δ ⊢ C ∙ R)
... | left  h = left (∧→L h)
... | right h = right λ{ (∧→L x) → h x }
isProvable (Γ , A₁ ∨ A₂ ⟶ B ∣ Δ ⊢ C ∙ R)
 with isProvable (Γ , A₁ ⟶ B , A₂ ⟶ B ∣ Δ ⊢ C ∙ R)
...  | left  h = left (∨→L h)
...  | right h = right λ{ (∨→L x) → h x}
isProvable (Γ , (A₁ ⟶ A₂) ⟶ B ∣ Δ ⊢ C ∙ R)
 with isProvable (Γ , A₂ ⟶ B , A₁ ∣ Δ ⊢ A₂ ∙ R) | isProvable (Γ , B ∣ Δ ⊢ C ∙ R)
... | left  h | left  t = left (→→L h t)
... | right h | _       = right λ{ (→→L x _) → h x }
... | _       | right h = right λ{ (→→L _ x) → h x }

-- Handle Pₙ → B for reduce resp. search mode.
isProvable (Γ , Pₙ@(Pvar n) ⟶ B ∣ Δ ⊢ C ∙ R)
 with isProvable (Γ , B ∣ Δ ⊢ C ∙ R)
    | isProvable (Γ ∣ Pₙ ⟶ B ,, Δ ⊢ C ∙ R)
    | dec-∈ Pₙ Γ
    | dec-∈ Pₙ Δ
... | right h | right t | _ | _ =
  right λ{ (P→L _ x) → h x
         ; (P→-f⟨ x) → t x
         }
... | _ | right h | right ∉Γ | right ∉Δ =
  right λ{ (P→L (left  ∈Γ) _) → ∉Γ ∈Γ
         ; (P→L (right ∈Δ) _) → ∉Δ ∈Δ
         ; (P→-f⟨ x)          → h x
         }
... | left  h | _      | left  ∈Γ | _        = left (P→L (left  ∈Γ) h)
... | left  h | _      | _        | left  ∈Δ = left (P→L (right ∈Δ) h)
... | _       | left h | _        | _        = left (P→-f⟨ h)
isProvable (Γ , Pₙ@(Pvar n) ⟶ B ∣ Δ ⊢ C ∙ S)
 with isProvable (Γ , B ∣ Δ ⊢ C ∙ R)
    | isProvable (Γ ∣ Pₙ ⟶ B ,, Δ ⊢ C ∙ S)
    | dec-∈ Pₙ Γ
    | dec-∈ Pₙ Δ
... | right h | right t | _ | _ =
  right λ{ (P→L _ x) → h x
         ; (continueSearch w) → t w
         }
... | _ | right h | right ∉Γ | right ∉Δ =
  right λ{ (P→L (left  ∈Γ) _) → ∉Γ ∈Γ
         ; (P→L (right ∈Δ) _) → ∉Δ ∈Δ
         ; (continueSearch w) → h w
         }
... | left  h | _      | left  ∈Γ | _        = left (P→L (left  ∈Γ) h)
... | left  h | _      | _        | left  ∈Δ = left (P→L (right ∈Δ) h)
... | _       | left h | _        | _        = left (continueSearch h)

-- These are all of the shift-left cases for search mode..
isProvable (Γ , Pvar n ∣ Δ ⊢ C ∙ S)
 with isProvable (Γ ∣ Pvar n ,, Δ ⊢ C ∙ S)
... | left  h = left (continueSearch h)
... | right h = right λ{ (continueSearch t) → h t }
isProvable (Γ , ⊤ ∣ Δ ⊢ C ∙ S)
 with isProvable (Γ ∣ ⊤ ,, Δ ⊢ C ∙ S)
... | left  h = left (continueSearch h)
... | right h = right λ{ (continueSearch t) → h t }
isProvable (Γ , ⊥ ∣ Δ ⊢ C ∙ S)
 with isProvable (Γ ∣ ⊥ ,, Δ ⊢ C ∙ S)
... | left  h = left (continueSearch h)
... | right h = right λ{ (continueSearch t) → h t }
isProvable (Γ , A ∧ B ∣ Δ ⊢ C ∙ S)
 with isProvable (Γ ∣ A ∧ B ,, Δ ⊢ C ∙ S)
... | left  h = left (continueSearch h)
... | right h = right λ{ (continueSearch t) → h t }
isProvable (Γ , A ∨ B ∣ Δ ⊢ C ∙ S)
 with isProvable (Γ ∣ A ∨ B ,, Δ ⊢ C ∙ S)
... | left  h = left (continueSearch h)
... | right h = right λ{ (continueSearch t) → h t }
isProvable (Γ , ⊤ ⟶ B ∣ Δ ⊢ C ∙ S)
 with isProvable (Γ ∣ ⊤ ⟶ B ,, Δ ⊢ C ∙ S)
... | left  h = left (continueSearch h)
... | right h = right λ{ (continueSearch t) → h t }
isProvable (Γ , ⊥ ⟶ B ∣ Δ ⊢ C ∙ S)
 with isProvable (Γ ∣ ⊥ ⟶ B ,, Δ ⊢ C ∙ S)
... | left  h = left (continueSearch h)
... | right h = right λ{ (continueSearch t) → h t }
isProvable (Γ , A₁ ∧ A₂ ⟶ B ∣ Δ ⊢ C ∙ S)
 with isProvable (Γ ∣ A₁ ∧ A₂ ⟶ B ,, Δ ⊢ C ∙ S)
... | left  h = left (continueSearch h)
... | right h = right λ{ (continueSearch t) → h t }
isProvable (Γ , A₁ ∨ A₂ ⟶ B ∣ Δ ⊢ C ∙ S)
 with isProvable (Γ ∣ A₁ ∨ A₂ ⟶ B ,, Δ ⊢ C ∙ S)
... | left  h = left (continueSearch h)
... | right h = right λ{ (continueSearch t) → h t }
isProvable (Γ , (A₁ ⟶ A₂) ⟶ B ∣ Δ ⊢ C ∙ S)
 with isProvable (Γ ∣ (A₁ ⟶ A₂) ⟶ B ,, Δ ⊢ C ∙ S)
... | left  h = left (continueSearch h)
... | right h = right λ{ (continueSearch t) → h t }
