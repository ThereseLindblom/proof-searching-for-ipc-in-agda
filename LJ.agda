open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Data.Empty using () renaming (⊥-elim to bot-elim) public
open import Prelude
  using ( 𝔹; true; false; _and_; _or_; _cond_;
          false-not-true; A∧B-t⇒A-t; A∧B-t⇒B-t; ∨-t₁; ∨-t₂; A∨B⇒EitherAB;
          List; _,_; _∈_; head; tail; _⊆_; ,-mono-⊆; ,-mono-r-⊆; ⊆-reflexive;
          Either; left; right; reduceEither; mapEither
        )
open import Prop using (Prop; Ctx; Pvar; ⊤; ⊥; _∧_; _∨_; _⟶_)

-----------------------------------------
-- LJ formalized in Agda. Section 3.3. --
-----------------------------------------

infix 3 _⊢_
data _⊢_ : Ctx → Prop → Set₁ where
  id  : ∀ {Γ} {n}
      → Pvar n ∈ Γ
        ---------- id
      → Γ ⊢ Pvar n

  ⊤R  : ∀ {Γ}
        ----- ⊤R
      → Γ ⊢ ⊤

  ⊥L  : ∀ {Γ} {C}
      → ⊥ ∈ Γ
        ----- ⊥L
      → Γ ⊢ C

  ∧R  : ∀ {Γ} {A B}
      → Γ ⊢ A
      → Γ ⊢ B
        --------- ∧R
      → Γ ⊢ A ∧ B

  ∧L₁ : ∀ {Γ} {A B C}
      → A ∧ B ∈ Γ
      → Γ , A ⊢ C
        ----- ∧L₁
      → Γ ⊢ C

  ∧L₂ : ∀ {Γ} {A B C}
      → A ∧ B ∈ Γ
      → Γ , B ⊢ C
        --------- ∧L₂
      → Γ ⊢ C 

  ∨R₁ : ∀ {Γ} {A B}
      → Γ ⊢ A
        --------- ∨R₁
      → Γ ⊢ A ∨ B

  ∨R₂ : ∀ {Γ} {A B}
      → Γ ⊢ B
        --------- ∨R₂
      → Γ ⊢ A ∨ B

  ∨L  : ∀ {Γ} {A B C}
      → A ∨ B ∈ Γ
      → Γ , A ⊢ C
      → Γ , B ⊢ C
        --------- ∨L
      → Γ ⊢ C

  →R  : ∀ {Γ} {A B}
      → Γ , A ⊢ B
        --------- →R
      → Γ ⊢ A ⟶ B

  →L  : ∀ {Γ} {A B C}
      → A ⟶ B ∈ Γ
      → Γ ⊢ A
      → Γ , B ⊢ C
        --------- →L
      → Γ ⊢ C

  cut : ∀ {Γ} {A C}
      → Γ ⊢ A
      → Γ , A ⊢ C
        --------- cut
      → Γ ⊢ C

------------------------------------
-- Structural rules. Section 3.4. --
------------------------------------

strong-id : ∀ {Γ} {A} → A ∈ Γ → Γ ⊢ A
strong-id {_} {Pvar n} h = id h
strong-id {_} {⊤} h = ⊤R
strong-id {_} {⊥} h = ⊥L h
strong-id {_} {A ∧ B} h =
  ∧R
    (∧L₁ h (strong-id head))
    (∧L₂ h (strong-id head))
strong-id {_} {A ∨ B} h =
  ∨L
    h
    (∨R₁ (strong-id head))
    (∨R₂ (strong-id head))
strong-id {_} {A ⟶ B} h =
  →R (→L (tail h) (strong-id head) (strong-id head))

strong-weaken : ∀ {Γ Δ} {C} → Γ ⊆ Δ → Γ ⊢ C → Δ ⊢ C
strong-weaken Γ⊆Δ (id h) = id (Γ⊆Δ h)
strong-weaken Γ⊆Δ ⊤R = ⊤R
strong-weaken Γ⊆Δ (⊥L h) = ⊥L (Γ⊆Δ h)
strong-weaken Γ⊆Δ (∧R 𝒟₁ 𝒟₂) =
  ∧R
    (strong-weaken Γ⊆Δ 𝒟₁)
    (strong-weaken Γ⊆Δ 𝒟₂)
strong-weaken Γ⊆Δ (∧L₁ h 𝒟₁) =
  ∧L₁
    (Γ⊆Δ h)
    (strong-weaken
      (,-mono-⊆ Γ⊆Δ)
      𝒟₁
    )
strong-weaken Γ⊆Δ (∧L₂ h 𝒟₁) =
  ∧L₂
    (Γ⊆Δ h)
    (strong-weaken
      (,-mono-⊆ Γ⊆Δ)
      𝒟₁
    )
strong-weaken Γ⊆Δ (∨R₁ 𝒟₁) = ∨R₁ (strong-weaken Γ⊆Δ 𝒟₁)
strong-weaken Γ⊆Δ (∨R₂ 𝒟₁) = ∨R₂ (strong-weaken Γ⊆Δ 𝒟₁)
strong-weaken Γ⊆Δ (∨L h 𝒟₁ 𝒟₂) =
  ∨L
    (Γ⊆Δ h)
    (strong-weaken (,-mono-⊆ Γ⊆Δ) 𝒟₁)
    (strong-weaken (,-mono-⊆ Γ⊆Δ) 𝒟₂)
strong-weaken Γ⊆Δ (→R 𝒟₁) =
  →R
    (strong-weaken
      (,-mono-⊆ Γ⊆Δ)
      𝒟₁
    )
strong-weaken Γ⊆Δ (→L h 𝒟₁ 𝒟₂) =
  →L
    (Γ⊆Δ h)
    (strong-weaken Γ⊆Δ 𝒟₁)
    (strong-weaken
      (,-mono-⊆ Γ⊆Δ)
      𝒟₂
    )
strong-weaken Γ⊆Δ (cut 𝒟₁ 𝒟₂) =
  cut
    (strong-weaken Γ⊆Δ 𝒟₁)
    (strong-weaken
      (,-mono-⊆ Γ⊆Δ)
      𝒟₂
    )

weaken : ∀ {Γ} {x C} → Γ ⊢ C → Γ , x ⊢ C
weaken {Γ} {x} = strong-weaken (,-mono-r-⊆ (⊆-reflexive refl))

contract : ∀ {Γ} {x C} → x ∈ Γ → Γ , x ⊢ C → Γ ⊢ C
contract h = strong-weaken (lemm h)
  where
  lemm : ∀ {Γ} {x y : Prop} → x ∈ Γ → y ∈ Γ , x → y ∈ Γ
  lemm h₁ head = h₁
  lemm _ (tail h₂) = h₂

exchange : ∀ {Γ} {A B C} → Γ , A , B ⊢ C → Γ , B , A ⊢ C
exchange {Γ} {A} {B} = strong-weaken lemm
  where
  lemm : ∀ {x} → x ∈ Γ , A , B → x ∈ Γ , B , A
  lemm head = tail head
  lemm (tail head) = head
  lemm (tail (tail h)) = tail (tail h)

----------------------------
-- Soundness. Section 3.5 --
----------------------------

Assignment : Set
Assignment = ℕ → 𝔹

⟦_⟧_ : Prop → Assignment → 𝔹
⟦ (Pvar n) ⟧ a = a n
⟦ ⊤ ⟧ _ = true
⟦ ⊥ ⟧ _ = false
⟦ A ∧ B ⟧ a = ⟦ A ⟧ a and  ⟦ B ⟧ a
⟦ A ∨ B ⟧ a = ⟦ A ⟧ a or   ⟦ B ⟧ a
⟦ A ⟶ B ⟧ a = ⟦ A ⟧ a cond ⟦ B ⟧ a

_satisfies_ : Assignment → Ctx → Set
a satisfies Γ = ∀ {γ} → γ ∈ Γ → ⟦ γ ⟧ a ≡ true

infix 4 _⊨_
_⊨_ : Ctx → Prop → Set
Γ ⊨ C = ∀ {a} → a satisfies Γ → ⟦ C ⟧ a ≡ true

val-dec : (φ : Prop) → (a : Assignment) → Either (⟦ φ ⟧ a ≡ true) (⟦ φ ⟧ a ≡ false)
val-dec (Pvar n) a with a n
...                | true = left refl
...                | false = right refl
val-dec ⊤ _ = left refl
val-dec ⊥ _ = right refl
val-dec (A ∧ B) a with val-dec A a | val-dec B a
...               | left  h        | left  t  = left  (cong₂ _and_ h t)
...               | left  h        | right t  = right (cong₂ _and_ h t)
...               | right h        | left  t  = right (cong₂ _and_ h t)
...               | right h        | right t  = right (cong₂ _and_ h t)
val-dec (A ∨ B) a with val-dec A a | val-dec B a
...               | left  h        | left  t  = left  (cong₂ _or_ h t)
...               | left  h        | right t  = left  (cong₂ _or_ h t)
...               | right h        | left  t  = left  (cong₂ _or_ h t)
...               | right h        | right t  = right (cong₂ _or_ h t)
val-dec (A ⟶ B) a with val-dec A a | val-dec B a
...               | left h         | left  t  = left  (cong₂ _cond_ h t)
...               | left h         | right t  = right (cong₂ _cond_ h t) 
...               | right h        | left  t  = left  (cong₂ _cond_ h t)
...               | right h        | right t  = left  (cong₂ _cond_ h t)

soundness : ∀ {Γ} {C} → Γ ⊢ C → Γ ⊨ C
soundness (id Pₙ∈Γ) a-sat-Γ = a-sat-Γ Pₙ∈Γ
soundness ⊤R _ = refl
soundness (⊥L ⊥∈Γ) a-sat-Γ = bot-elim (false-not-true refl (a-sat-Γ ⊥∈Γ))
soundness {Γ} {A ∧ B} (∧R 𝒟₁ 𝒟₂) a-sat-Γ = cong₂ _and_ (Γ⊨A a-sat-Γ) (Γ⊨B a-sat-Γ)
  where
  Γ⊨A : Γ ⊨ A
  Γ⊨A = soundness 𝒟₁

  Γ⊨B : Γ ⊨ B
  Γ⊨B = soundness 𝒟₂
soundness {Γ} {C} (∧L₁ {_} {A} {B} A∧B∈Γ 𝒟₁) {f} a-sat-Γ = ΓA⊨C a-sat-ΓA
  where
  ΓA⊨C : Γ , A ⊨ C
  ΓA⊨C = soundness 𝒟₁

  a-sat-ΓA : f satisfies (Γ , A)
  a-sat-ΓA head = A∧B-t⇒A-t (a-sat-Γ A∧B∈Γ)
  a-sat-ΓA (tail h) = a-sat-Γ h
soundness {Γ} {C} (∧L₂ {_} {A} {B} A∧B∈Γ 𝒟₁) {f} a-sat-Γ = ΓB⊨C a-sat-ΓB
  where
  ΓB⊨C : Γ , B ⊨ C
  ΓB⊨C = soundness 𝒟₁

  a-sat-ΓB : f satisfies (Γ , B)
  a-sat-ΓB head = A∧B-t⇒B-t (a-sat-Γ A∧B∈Γ)
  a-sat-ΓB (tail h) = a-sat-Γ h
soundness (∨R₁ 𝒟₁) a-sat-Γ = ∨-t₁ (soundness 𝒟₁ a-sat-Γ)
soundness (∨R₂ 𝒟₁) a-sat-Γ = ∨-t₂ (soundness 𝒟₁ a-sat-Γ)
soundness {Γ} {C} (∨L {_} {A} {B} A∨B∈Γ 𝒟₁ 𝒟₂) a-sat-Γ = reduceEither (mapEither
  (λ A-t → soundness 𝒟₁ λ{ head → A-t ; (tail h) → a-sat-Γ h})
  (λ B-t → soundness 𝒟₂ λ{ head → B-t ; (tail h) → a-sat-Γ h})
  (A∨B⇒EitherAB (a-sat-Γ A∨B∈Γ)))
soundness (→R {Γ} {A} {B} 𝒟₁) {a} a-sat-Γ with val-dec A a
... | left  A-t = cong₂ _cond_ A-t (ΓA⊨B a-sat-ΓA)
  where
  ΓA⊨B : Γ , A ⊨ B
  ΓA⊨B = soundness 𝒟₁

  a-sat-ΓA : a satisfies (Γ , A)
  a-sat-ΓA head     = A-t
  a-sat-ΓA (tail h) = a-sat-Γ h
... | right A-f = cong (_cond (⟦ B ⟧ a)) A-f
soundness {Γ} {C} (→L {_} {A} {B} A→B∈Γ 𝒟₁ 𝒟₂) {a} a-sat-Γ = C-t
  where
  -- Γ ⊨ A by inductuve hypothesis.
  Γ⊨A : Γ ⊨ A
  Γ⊨A = soundness 𝒟₁

  -- Γ, B ⊨ C by inductuve hypothesis.
  ΓB⊨C : Γ , B ⊨ C
  ΓB⊨C = soundness 𝒟₂

  -- A valuates to true since Γ ⊨ A.
  A-t : ⟦ A ⟧ a ≡ true
  A-t = Γ⊨A a-sat-Γ

  -- A → B valuates to true since A → B ∈ Γ.
  A→B-t : ⟦ A ⟶ B ⟧ a ≡ true
  A→B-t = a-sat-Γ A→B∈Γ

  -- B valuates to true since A and A → B valuates to true.
  B-t : ⟦ B ⟧ a ≡ true
  B-t with val-dec B a
  ...    | left  A-t = A-t
  ...    | right B-f = bot-elim (false-not-true (cong₂ _cond_ A-t B-f) A→B-t)

  -- Therefore a satisfies Γ, B.
  a-sat-ΓB : a satisfies (Γ , B)
  a-sat-ΓB head = B-t
  a-sat-ΓB (tail h) = a-sat-Γ h

  -- Finally, C valuates to true.
  C-t : ⟦ C ⟧ a ≡ true
  C-t = ΓB⊨C a-sat-ΓB
soundness (cut {Γ} {A} {C} 𝒟₁ 𝒟₂) {a} a-sat-Γ = C-t
  where
  Γ⊨A : Γ ⊨ A
  Γ⊨A = soundness 𝒟₁

  ΓA⊨C : Γ , A ⊨ C
  ΓA⊨C = soundness 𝒟₂

  A-t : ⟦ A ⟧ a ≡ true
  A-t = Γ⊨A a-sat-Γ

  C-t : ⟦ C ⟧ a ≡ true
  C-t = ΓA⊨C λ{ head → A-t ; (tail h) → a-sat-Γ h }
