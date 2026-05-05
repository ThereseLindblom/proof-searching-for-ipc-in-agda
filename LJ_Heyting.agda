
module proof-searching-for-ipc-in-agda.LJ_Heyting where

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
-- Soundness.             --
----------------------------

-- Code by Anders below. With some comments

module Soundness
      -- Parametrize by a set (carrier of Heyting algebra)
      (H : Set)
      (⊤h : H)
      (⊥h : H)
      (_≤_ : H → H → Set)
      --partial order axioms
      (≤-refl : (a : H) → a ≤ a)
      (≤-antisym : (a b : H) → a ≤ b → b ≤ a → a ≡ b)
      (≤-trans : (a b c : H) → a ≤ b → b ≤ c → a ≤ c)
      --top H1
      (≤-top : (a : H) → a ≤ ⊤h)
      --bot H5
      (≤-bot : (a : H) → ⊥h ≤ a)

      -- Operations:
      (_∧h_ : H → H → H)
      (_∨h_ : H → H → H)
      (_⟶h_ : H → H → H)
      

      -- Heyting algebra axioms/laws:

      (H2 : (a b : H) → (a ∧h b) ≤ a)
      (H3 : (a b : H) → (a ∧h b) ≤ b)
      (H4 : (a b c : H) → c ≤ a → c ≤ b → c ≤ (a ∧h b))
      (H6 : (a b : H) → a ≤ (a ∨h b))
      (H7 : (a b : H) → b ≤ (a ∨h b))
      (H8 : (a b c : H) → a ≤ c → b ≤ c → (a ∨h b) ≤ c)
      (H9 : (a b c : H) → c ≤ (a ⟶h b) ≡ (c ∧h a) ≤ b)
      (∧h-assoc : (a b c : H) → a ∧h (b ∧h c) ≡ (a ∧h b) ∧h c)
      (∨h-assoc : (a b c : H) → a ∨h (b ∨h c) ≡ (a ∨h b) ∨h c)
      --(∨h-distrib-∧h : (a b c : H) → a ∨h (b ∧h c) ≡ (a ∨h b) ∧h (a ∨h c)) lägg lemma nere
      --(∧h-distrib-∨h : (a b c : H) → a ∧h (b ∨h c) ≡ (a ∧h b) ∨h (a ∧h c)) lägg lemma nere

      -- With the above parameters we can now start the proof, so we
      -- start the module using where:
  where

  -- TODO: You might need to prove lemmas about Heyting algebras here.
  -- This can be done on a call by need basis by seeing what you need in the proof below




  Assignment : Set
  Assignment = ℕ → H

  〚_〛_ : Prop → Assignment → H
  〚 Pvar x 〛 a = a x
  〚 ⊤ 〛 a = ⊤h
  〚 ⊥ 〛 a = ⊥h
  〚 x ∧ y 〛 a = (〚 x 〛 a) ∧h (〚 y 〛 a)
  〚 x ∨ y 〛 a = (〚 x 〛 a) ∨h (〚 y 〛 a)
  〚 x ⟶ y 〛 a = (〚 x 〛 a) ⟶h (〚 y 〛 a)

  _satisfies_ : Assignment → Ctx → Set
  a satisfies Γ = ∀ {γ} → γ ∈ Γ → 〚 γ 〛 a ≡ ⊤h 

  infix 4 _⊨_
  _⊨_ : Ctx → Prop → Set
  Γ ⊨ C = ∀ {a} → a satisfies Γ → 〚 C 〛 a ≡ ⊤h

  -- TODO: Is something like this needed for soundness? How to state
  -- it? Probably not true with top and bottom element instead of holes
  --val-dec : (φ : Prop) → (a : Assignment) → Either (〚 φ 〛 a ≡ {!!}) (〚 φ 〛 a ≡ {!!})
  --val-dec = {!!}

  -- The final boss
  soundness : ∀ {Γ} {C} → Γ ⊢ C → Γ ⊨ C
  soundness (id x) a_sat_Γ = a_sat_Γ x
  soundness ⊤R a_sat_Γ = refl
  soundness {Γ} {C = C} (⊥L x) {a} a_sat_Γ = ≤-antisym (〚 C 〛 a) ⊤h (≤-top (〚 C 〛 a)) {!!}
  soundness {Γ} (∧R {A = A} {B} d d₁) {a} a_sat_Γ = {!!}
  soundness {Γ} {C = C} (∧L₁ {A = A} {B} x d) {a} a_sat_Γ = {!!}
  soundness (∧L₂ x d) a_sat_Γ = {!!}
  soundness (∨R₁ d) a_sat_Γ = {!!}
  soundness (∨R₂ d) a_sat_Γ = {!!}
  soundness (∨L x d d₁) a_sat_Γ = {!!}
  soundness (→R d) a_sat_Γ = {!!}
  soundness (→L x d d₁) a_sat_Γ = {!!}
  soundness (cut d d₁) a_sat_Γ = {!!}



-- TODO: once the above is finished you should be able to easily check
-- that Bool is a Heyting algebra and instantiate the above module
-- with it, hence getting the result in Section 3.5 of Emmas thesis as
-- a special case.
