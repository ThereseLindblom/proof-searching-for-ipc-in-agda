module Translate where

open import Agda.Primitive using (Level)
open import Data.List.Relation.Binary.Subset.Propositional.Properties
  using (⊆-trans; ++⁺ˡ)
  renaming (xs⊆xs++ys to ++-mono-r-⊆; xs⊆ys++xs to ++-mono-l-⊆)
  public
open import Prelude
  using ( Either; left; right
        ; List; ∅; _,_; _++_; _∈_; head; tail; _⊆_
        )
open import Prop using (Prop; Pvar; ⊤; ⊥; _∧_; _∨_; _⟶_)
open import LJ using (_⊢_; strong-id; strong-weaken)
open import LJf
  using ( _∣_⊢_∙_; _∈LJf; _,,_
        ; id; id-f⟨
        ; ⊤R; ⊤L
        ; ⊥L
        ; ∧R; ∧L
        ; ∨R₁; ∨R₂; ∨L
        ; →R
        ; P→L; ⊤→L; ⊥→L; ∧→L; ∨→L; →→L
        ; P→-f⟨
        ; initSearch; continueSearch
        )

module ⊆-Reasoning {a : Level} {A : Set a} where
  open import Data.List.Relation.Binary.Subset.Propositional.Properties
    using (⊆-preorder)
  import Relation.Binary.PropositionalEquality as ≡

  open import Relation.Binary.Reasoning.Preorder (⊆-preorder A)
    as ≲-reasoning
    hiding (step-≈; step-≈˘; step-≈-⟩; step-≈-⟨; step-≲; step-∼)
    renaming (≲-go to ⊆-go)
    public

  open import Relation.Binary.Reasoning.Syntax
  open import Relation.Binary.Reasoning.Base.Single as Base
  
  open begin-membership-syntax ≲-reasoning._IsRelatedTo_ _∈_ (λ x → ≲-reasoning.begin x) public
  open ⊆-syntax ≲-reasoning._IsRelatedTo_ ≲-reasoning._IsRelatedTo_ ⊆-go public
open ⊆-Reasoning

,-mono-⊆ : ∀ {A : Set} {Γ Δ : List A} {x : A} → Γ ⊆ Δ → Γ , x ⊆ Δ , x
,-mono-⊆ Γ⊆Δ head = head
,-mono-⊆ Γ⊆Δ (tail x∈Γ) = tail (Γ⊆Δ x∈Γ)

,-mono-r-⊆ : ∀ {A : Set} {Γ Δ : List A} {x : A} → Γ ⊆ Δ → Γ ⊆ Δ , x
,-mono-r-⊆ Γ⊆Δ h = tail (Γ⊆Δ h)

,-mono-r-⊆' : ∀ {A : Set} {Γ : List A} {x : A} → Γ ⊆ Γ , x
,-mono-r-⊆' h = tail h

lemma₁ : ∀ Γ Δ (x : Prop) → x ∈ Γ → x ∈ Γ ++ Δ
lemma₁ Γ Δ _ = ++-mono-r-⊆ Γ Δ

lemma₂ : ∀ {Γ : List Prop} → Γ ++ ∅ ⊆ ∅ ++ Γ
lemma₂ {Γ@(Γ' , γ)} =
  begin
     Γ ++ ∅               ≡⟨⟩
     (Γ' , γ) ++ ∅        ≡⟨⟩
     (Γ' ++ ∅) , γ        ⊆⟨ ,-mono-⊆ lemma₂ ⟩
     (∅ ++ Γ') , γ        ≡⟨⟩
     (Γ' , γ)             ≡⟨⟩
     ∅ ++ (Γ' , γ)        ≡⟨⟩
     ∅ ++ Γ
  ∎

lemma₃ : ∀ Γ Δ (B X : Prop) → Γ , B ++ Δ ⊆ (Γ , X ++ Δ) , B
lemma₃ Γ Δ B X =
  begin
    Γ , B ++ Δ               ≡⟨⟩
    (Γ ++ Δ) , B             ⊆⟨ ,-mono-⊆ (++⁺ˡ Δ ,-mono-r-⊆') ⟩
    (Γ , X ++ Δ) , B
   ∎

lemma₄ : ∀ Γ Δ (X : Prop) → Γ ++ (Δ , X) ⊆ (Γ , X) ++ Δ
lemma₄ ∅ Δ X =
  begin
    ∅ ++ (Δ , X)  ≡⟨⟩
    Δ , X         ≡⟨⟩
    (∅ , X) ++ Δ
  ∎
lemma₄ (Γ , γ) Δ X = 
  begin
    Γ , γ ++ Δ , X     ≡⟨⟩
    (Γ ++ Δ , X) , γ     ⊆⟨ ,-mono-⊆ (lemma₄ Γ Δ X) ⟩
    (Γ , X ++ Δ) , γ     ≡⟨⟩
    (Γ , X , γ ++ Δ)     ⊆⟨ ++⁺ˡ Δ (λ{ head → tail head
                                    ; (tail head) → head
                                    ; (tail (tail h)) → tail (tail h)
                                    })
                          ⟩
    (Γ , γ , X) ++ Δ
  ∎

translate : ∀ {Γ Δ} {C} {m} → Γ ∣ Δ ⊢ C ∙ m ∈LJf → Γ ++ Δ ⊢ C
translate (initSearch _ 𝒟₁) = strong-weaken lemma₂ (translate 𝒟₁)
translate (continueSearch {Γ} {Δ} {A} 𝒟₁) =
  strong-weaken (lemma₄ Γ Δ A) (translate 𝒟₁)
translate (id-f⟨ {Γ} {Δ} {n} 𝒟₁) =
  strong-weaken
  (begin
    Γ ++ Pvar n ,, Δ        ≡⟨⟩
    Γ ++ (Δ , Pvar n)       ≡⟨⟩
    Γ ++ (Δ , Pvar n)       ⊆⟨ lemma₄ Γ Δ (Pvar n) ⟩
    (Γ , Pvar n) ++ Δ
   ∎)
  (translate 𝒟₁)
translate (P→-f⟨ {Γ} {Δ} {n} {B} 𝒟₁) =
  strong-weaken
  (begin
    Γ ++ Pvar n ⟶ B ,, Δ    ≡⟨⟩
    Γ ++ (Δ , Pvar n ⟶ B)   ⊆⟨ lemma₄ Γ Δ (Pvar n ⟶ B) ⟩
    (Γ , Pvar n ⟶ B) ++ Δ
   ∎)
  (translate 𝒟₁)
translate {Γ , Pₙ} {Δ} id = LJ.id (lemma₁ (Γ , Pₙ) Δ Pₙ head)
translate ⊤R = LJ.⊤R
translate {Γ , ⊤} {Δ} (⊤L 𝒟₁) =
  strong-weaken
  (begin
    Γ ++ Δ                   ⊆⟨ ++⁺ˡ Δ tail ⟩
    (Γ , ⊤) ++ Δ
   ∎)
  (translate 𝒟₁)
translate {Γ , ⊥} {Δ} ⊥L = LJ.⊥L (lemma₁ (Γ , ⊥) Δ ⊥ head)
translate (∧R 𝒟₁ 𝒟₂) =
  LJ.∧R
    (strong-weaken
      lemma₂
      (translate 𝒟₁)
    )
    (strong-weaken
      lemma₂
      (translate 𝒟₂)
    )
translate {Γ@(Γ' , A ∧ B)} {Δ} (∧L 𝒟₁) =
  LJ.∧L₁
    (++-mono-r-⊆ Γ Δ head)
    (LJ.∧L₂
      (⊆-trans (++-mono-r-⊆ Γ Δ) ,-mono-r-⊆' head)
      (strong-weaken
        (begin
          Γ' , A , B ++ Δ            ≡⟨⟩
          (Γ' ++ Δ) , A , B          ⊆⟨ ,-mono-⊆-2 (++⁺ˡ Δ ,-mono-r-⊆' ) ⟩
          (Γ' , (A ∧ B) ++ Δ) , A , B
        ∎)
        (translate 𝒟₁)
      )
    )
  where
  ,-mono-⊆-2 : ∀ {x y : Prop} {Γ Δ} → Γ ⊆ Δ → Γ , x , y ⊆ Δ , x , y
  ,-mono-⊆-2 h = ,-mono-⊆ (,-mono-⊆ h)
translate (∨R₁ 𝒟₁) =
  LJ.∨R₁ (strong-weaken lemma₂ (translate 𝒟₁))
translate (∨R₂ 𝒟₁) =
  LJ.∨R₂ (strong-weaken lemma₂ (translate 𝒟₁))
translate {Γ' , A ∨ B} {Δ} (∨L 𝒟₁ 𝒟₂) =
  LJ.∨L (lemma₁ (Γ' , A ∨ B) Δ (A ∨ B) head)
    (strong-weaken (lemm A) (translate 𝒟₁))
    (strong-weaken (lemm B) (translate 𝒟₂))
    where
    lemm : ∀ X → Γ' , X ++ Δ ⊆ (Γ' , A ∨ B ++ Δ) , X
    lemm X =
      begin
        Γ' , X ++ Δ               ≡⟨⟩
        (Γ' ++ Δ), X              ⊆⟨ ,-mono-⊆ ,-mono-r-⊆' ⟩
        ((Γ' ++ Δ), A ∨ B), X     ≡⟨⟩
        (Γ' , A ∨ B ++ Δ) , X
      ∎
translate (→R 𝒟₁) =
  LJ.→R (strong-weaken (,-mono-⊆ lemma₂) (translate 𝒟₁))
translate {Γ' , Pₙ ⟶ B} {Δ} (P→L (left h) 𝒟₁) =
  LJ.→L
    (lemma₁ (Γ' , Pₙ ⟶ B) Δ (Pₙ ⟶ B) head)
    (LJ.id (++-mono-r-⊆ (Γ' , Pₙ ⟶ B) Δ (tail h)))
    (strong-weaken
      (lemma₃ Γ' Δ B (Pₙ ⟶ B))
      (translate 𝒟₁)
    )
translate {Γ' , Pₙ ⟶ B} {Δ} (P→L (right h) 𝒟₁) =
  LJ.→L
    (lemma₁ (Γ' , Pₙ ⟶ B) Δ (Pₙ ⟶ B) head)
    (LJ.id (++-mono-l-⊆ Δ (Γ' , Pₙ ⟶ B) h))
    (strong-weaken
      (lemma₃ Γ' Δ B (Pₙ ⟶ B))
      (translate 𝒟₁)
    )
translate {Γ' , ⊤ ⟶ B} {Δ} (⊤→L 𝒟₁) =
  LJ.→L
    (lemma₁ (Γ' , ⊤ ⟶ B) Δ (⊤ ⟶ B) head)
    LJ.⊤R
    (strong-weaken (lemma₃ Γ' Δ B (⊤ ⟶ B)) (translate 𝒟₁))
translate {Γ' , ⊥ ⟶ B} {Δ} (⊥→L 𝒟₁) =
  strong-weaken (++⁺ˡ Δ ,-mono-r-⊆') (translate 𝒟₁)
translate {Γ' , A₁ ∧ A₂ ⟶ B} {Δ} {C} (∧→L 𝒟₁) =
  LJ.cut
    (LJ.→R
      (LJ.→R
        (LJ.→L
          (tail (tail head))
          (LJ.∧R
            (strong-id (tail head))
            (strong-id head)
          )
          (strong-id head)
        )
      )
    )
    (strong-weaken
      (λ{ head → head
        ; (tail h) → tail (tail h)
        })
      (translate 𝒟₁))
translate (∨→L 𝒟₁) =
  LJ.cut
    (LJ.→R
      (LJ.→L
        (tail head)
        (LJ.∨R₂ (strong-id head))
        (strong-id head)
      )
    )
    (LJ.cut
      (LJ.→R
        (LJ.→L
          (tail (tail head))
          (LJ.∨R₁ (strong-id head))
          (strong-id head))
      )
      (strong-weaken
        (λ{ head → tail head
          ; (tail head) → head
          ; (tail (tail h)) → tail (tail (tail h))
          }
        )
        (translate 𝒟₁))
    )
translate (→→L {Γ} {Δ} {A₁} {A₂} {B} 𝒟₁ 𝒟₂) =
  LJ.→L
    head
    (LJ.→R
      (LJ.cut
        (LJ.→R
          (LJ.→L
            (tail (tail head))
            (LJ.→R (strong-id (tail head)))
            (strong-id head)
          )
        )
        (strong-weaken
          (λ{ head → tail head
            ; (tail head) → head
            ; (tail (tail h)) → tail (tail (tail h))
            }
          )
        (translate 𝒟₁))
      )
    )
    (strong-weaken
      (,-mono-⊆ ,-mono-r-⊆')
      (translate 𝒟₂)
    )
