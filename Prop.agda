open import Prelude
  using ( Either; left; right; mapEither;
          ℕ-dec-≡;
          List; ∅; _,_; _∈_; _∉_; head; tail
        )
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; subst)
  renaming (sym to ≡-sym)

module Prop where

data Prop : Set where
  Pvar : ℕ → Prop
  ⊤    : Prop
  ⊥    : Prop
  _∧_  : Prop → Prop → Prop
  _∨_  : Prop → Prop → Prop
  _⟶_  : Prop → Prop → Prop
infix 9 _∧_
infix 9 _∨_
infix 8 _⟶_

Ctx : Set
Ctx = List Prop

prop-dec-≡ : (A : Prop) → (B : Prop) → Either (A ≡ B) (A ≢ B)
prop-dec-≡ (Pvar n) (Pvar m) with ℕ-dec-≡ n m
prop-dec-≡ (Pvar n) (Pvar m)    | (left  n≡m) = left (cong Pvar n≡m)
prop-dec-≡ (Pvar n) (Pvar m)    | (right n≢m) = right λ { refl → n≢m refl }
prop-dec-≡ ⊤ ⊤ = left refl
prop-dec-≡ ⊥ ⊥ = left refl
prop-dec-≡ (A ∧ B) (C ∧ D) with prop-dec-≡ A C | prop-dec-≡ B D
prop-dec-≡ (A ∧ B) (C ∧ D)    | (left A≡C)     | (left B≡D)  =
  left (cong₂ _∧_ A≡C B≡D)
prop-dec-≡ (A ∧ B) (C ∧ D)    | (right A≢C)    | _           =
  right λ { refl → A≢C refl}
prop-dec-≡ (A ∧ B) (C ∧ D)    | _              | (right A≢C) =
  right λ { refl → A≢C refl}
prop-dec-≡ (_ ∧ _) (_ ∨ _) = right λ()
prop-dec-≡ (_ ∧ _) (_ ⟶ _) = right λ()
prop-dec-≡ (A ∨ B) (C ∨ D) with prop-dec-≡ A C | prop-dec-≡ B D
prop-dec-≡ (A ∨ B) (C ∨ D)    | (left A≡C)     | (left B≡D) = left (cong₂ _∨_ A≡C B≡D)
prop-dec-≡ (A ∨ B) (C ∨ D)    | (right A≢C)    | _           = 
  right λ { refl → A≢C refl}
prop-dec-≡ (A ∨ B) (C ∨ D)    | _              | (right A≢C) =
  right λ { refl → A≢C refl}
prop-dec-≡ (A ⟶ B) (C ⟶ D) with prop-dec-≡ A C | prop-dec-≡ B D
prop-dec-≡ (A ⟶ B) (C ⟶ D)    | (left A≡C)     | (left B≡D) = left (cong₂ _⟶_ A≡C B≡D)
prop-dec-≡ (A ⟶ B) (C ⟶ D)    | (right A≢C)    | _           =
  right λ { refl → A≢C refl}
prop-dec-≡ (A ⟶ B) (C ⟶ D)    | _              | (right A≢C) =
  right λ { refl → A≢C refl}
prop-dec-≡ (Pvar x) ⊤        = right λ()
prop-dec-≡ (Pvar x) ⊥        = right λ()
prop-dec-≡ (Pvar x) (B ∧ B₁) = right λ()
prop-dec-≡ (Pvar x) (B ∨ B₁) = right λ()
prop-dec-≡ (Pvar x) (B ⟶ B₁) = right λ()
prop-dec-≡ ⊤ (Pvar x)        = right λ()
prop-dec-≡ ⊤ ⊥               = right λ()
prop-dec-≡ ⊤ (B ∧ B₁)        = right λ()
prop-dec-≡ ⊤ (B ∨ B₁)        = right λ()
prop-dec-≡ ⊤ (B ⟶ B₁)        = right λ()
prop-dec-≡ ⊥ (Pvar x)        = right λ()
prop-dec-≡ ⊥ ⊤               = right λ()
prop-dec-≡ ⊥ (B ∧ B₁)        = right λ()
prop-dec-≡ ⊥ (B ∨ B₁)        = right λ()
prop-dec-≡ ⊥ (B ⟶ B₁)        = right λ()
prop-dec-≡ (A ∧ A₁) (Pvar x) = right λ()
prop-dec-≡ (A ∧ A₁) ⊤        = right λ()
prop-dec-≡ (A ∧ A₁) ⊥        = right λ()
prop-dec-≡ (A ∨ A₁) (Pvar x) = right λ()
prop-dec-≡ (A ∨ A₁) ⊤        = right λ()
prop-dec-≡ (A ∨ A₁) ⊥        = right λ()
prop-dec-≡ (A ∨ A₁) (B ∧ B₁) = right λ()
prop-dec-≡ (A ∨ A₁) (B ⟶ B₁) = right λ()
prop-dec-≡ (A ⟶ A₁) (Pvar x) = right λ()
prop-dec-≡ (A ⟶ A₁) ⊤        = right λ()
prop-dec-≡ (A ⟶ A₁) ⊥        = right λ()
prop-dec-≡ (A ⟶ A₁) (B ∧ B₁) = right λ()
prop-dec-≡ (A ⟶ A₁) (B ∨ B₁) = right λ()

dec-∈ : (φ : Prop) → (Γ : List Prop) → Either (φ ∈ Γ) (φ ∉ Γ)
dec-∈ _ ∅ = right λ()
dec-∈ φ (Γ , ψ) with prop-dec-≡ φ ψ
dec-∈ φ (Γ , ψ)    | left  φ≡ψ = left (subst (λ x → x ∈ Γ , ψ) (≡-sym φ≡ψ) head)
dec-∈ φ (Γ , ψ)    | right φ≢ψ = mapEither tail
                                           (λ { φ∉Γ head → φ≢ψ refl
                                              ; φ∉Γ (tail φ∈Γ) → φ∉Γ φ∈Γ
                                              })
                                           (dec-∈ φ Γ)
