module Prelude where

open import Agda.Primitive using (Level; lzero)
open import Data.Nat using (ℕ; suc; zero; _<_)
open import Data.Product using (_×_) renaming (_,_ to pair)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Relation.Binary using (Rel)
open import Induction.WellFounded using (Acc; acc; WellFounded)
open import Data.Nat.Base using (_<′_; ≤′-reflexive; ≤′-step; <′-base; <′-step)
open import Data.Nat.Properties using (<⇒<′)

-----------------
-- Either type --
-----------------

open import Data.Sum
  renaming (_⊎_ to Either; inj₁ to left; inj₂ to right)
  public

mapEither = Data.Sum.map

reduceEither : ∀ {a} {A : Set a} → Either A A → A
reduceEither (left  x) = x
reduceEither (right x) = x

ℕ-dec-≡ : (n : ℕ) → (m : ℕ) → Either (n ≡ m) (n ≢ m)
ℕ-dec-≡ zero zero = left refl
ℕ-dec-≡ (suc _) zero = right λ()
ℕ-dec-≡ zero (suc _) = right λ()
ℕ-dec-≡ (suc n) (suc m) with ℕ-dec-≡ n m
ℕ-dec-≡ _ _                | (left  n≡m) = left (cong suc n≡m)
ℕ-dec-≡ _ _                | (right n≢m) = right λ{ refl → n≢m refl}

--------------
-- Booleans --
--------------

open import Data.Bool
  using (true; false)
  renaming (Bool to 𝔹; _∧_ to _and_; _∨_ to _or_)
  public

infix 5 _cond_
_cond_ : 𝔹 → 𝔹 → 𝔹
true cond false = false
_    cond _     = true

-- If x is false then x is not true.
false-not-true : ∀ {x} → x ≡ false → x ≢ true
false-not-true refl ()

-- If A and B is true then A is true
A∧B-t⇒A-t : {b₁ b₂ : 𝔹} → b₁ and b₂ ≡ true → b₁ ≡ true
A∧B-t⇒A-t {true} {true} _ = refl

-- If A and B is true then B is true
A∧B-t⇒B-t : {b₁ b₂ : 𝔹} → b₁ and b₂ ≡ true → b₂ ≡ true
A∧B-t⇒B-t {true} {true} _ = refl

-- If A is true then A or B is true.
∨-t₁ : {b₁ b₂ : 𝔹} → b₁ ≡ true → b₁ or b₂ ≡ true
∨-t₁ {true} {_} _ = refl

-- If B is true then A or B is true.
∨-t₂ : {b₁ b₂ : 𝔹} → b₂ ≡ true → b₁ or b₂ ≡ true
∨-t₂ {true}  {true} _ = refl
∨-t₂ {false} {true} _ = refl

-- If A ∨ B is true then A is true or B is true
A∨B⇒EitherAB : {b₁ b₂ : 𝔹} → b₁ or b₂ ≡ true → Either (b₁ ≡ true) (b₂ ≡ true)
A∨B⇒EitherAB {true} {_} _ = left  refl
A∨B⇒EitherAB {_} {true} _ = right refl

-----------
-- Lists --
-----------

open import Data.List
  using (List)
  renaming ([] to ∅)
  public

infixl 7 _,_
pattern _,_ xs x = Data.List._∷_ x xs

infix 6 _++_
_++_ : {a : Level} {A : Set a} -> List A -> List A -> List A
_++_ = Data.List._++_

open import Data.List.Membership.Propositional using (_∈_; _∉_) public
open import Data.List.Relation.Unary.Any using (here; there)

pattern head = here refl
pattern tail x∈xs = there x∈xs

------------------------------
-- Subset relation on lists --
------------------------------

open import Data.List.Relation.Binary.Subset.Propositional
  using (_⊆_) public
open import Data.List.Relation.Binary.Subset.Propositional.Properties
  using (⊆-reflexive; ⊆-trans; ++⁺ˡ)
  renaming (xs⊆xs++ys to ++-mono-r-⊆; xs⊆ys++xs to ++-mono-l-⊆)
  public

,-mono-⊆ : ∀ {A : Set} {Γ Δ : List A} {x : A} → Γ ⊆ Δ → Γ , x ⊆ Δ , x
,-mono-⊆ Γ⊆Δ head = head
,-mono-⊆ Γ⊆Δ (tail x∈Γ) = tail (Γ⊆Δ x∈Γ)

,-mono-r-⊆ : ∀ {A : Set} {Γ Δ : List A} {x : A} → Γ ⊆ Δ → Γ ⊆ Δ , x
,-mono-r-⊆ Γ⊆Δ h = tail (Γ⊆Δ h)

,-mono-r-⊆' : ∀ {A : Set} {Γ : List A} {x : A} → Γ ⊆ Γ , x
,-mono-r-⊆' h = tail h

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

----------------------
-- Well-foundedness --
----------------------

-- A lexicographically ordered pair.
infix 4 _<×<_
data _<×<_ : Rel (ℕ × ℕ) lzero where
  lexical-fst : ∀ {a b x y} → a < x         → (pair a b) <×< (pair x y)
  lexical-snd : ∀ {a b x y} → a ≡ x → b < y → (pair a b) <×< (pair x y)

ℕ′-wf : WellFounded _<′_
ℕ′-wf n = acc (aux n)
  where
  aux : ∀ n {m} → m <′ n → Acc _<′_ m
  aux (suc n) {m} (≤′-reflexive refl) = ℕ′-wf m
  aux (suc n) {m} (≤′-step m<n) = aux n m<n

subrelation-wf : {a ℓ₁ ℓ₂ : Level} {A : Set a} {_<₁_ : Rel A ℓ₁} {_<₂_ : Rel A ℓ₂}
               (<₁⇒<₂ : ∀ {x y} → x <₁ y → x <₂ y)
               → WellFounded _<₂_ → WellFounded _<₁_
subrelation-wf {_<₁_ = _<₁_} {_<₂_ = _<₂_} <₁⇒<₂ wf = λ x → accessible (wf x)
  where
  accessible : ∀ {x} → Acc _<₂_ x → Acc _<₁_ x
  accessible (acc rs) = acc λ y<x → accessible (rs (<₁⇒<₂ y<x))

ℕ-wf : WellFounded _<_
ℕ-wf = subrelation-wf <⇒<′ ℕ′-wf


-- ℕ × ℕ is accessible.
ℕ×ℕ-acc : ∀ {x y}
        → Acc _<_ x
        → Acc _<_ y
        → ∀ {u v} → (pair u v) <×< (pair x y)
        → (Acc _<×<_) (pair u v)
ℕ×ℕ-acc (acc rec₁) acc₂ (lexical-fst u<x) =
  acc (ℕ×ℕ-acc (rec₁ u<x) (ℕ-wf _))
ℕ×ℕ-acc acc₁ (acc rec₂) (lexical-snd refl v<y) =
  acc (ℕ×ℕ-acc acc₁ (rec₂ v<y))

-- ℕ × ℕ is well-founded.
ℕ×ℕ-wf : WellFounded _<×<_
ℕ×ℕ-wf (pair x y) = acc (ℕ×ℕ-acc (ℕ-wf x) (ℕ-wf y))
