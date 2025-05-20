module Examples where

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation.Core using (¬_) public
open import Prelude using (Either; left; right; mapEither; List; ∅; _,_)
open import Prop using (Prop; Pvar; ⊤; ⊥; _∧_; _∨_; _⟶_; prop-dec-≡; dec-∈)
open import LJf
  using ( SequentWithCursorAndMode; _∣_⊢_∙_; Mode; S; R; derivationFor; _,,_; isProvable; _∈LJf
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
open import Translate using (translate)

P₁ : Prop
P₁ = Pvar 1

P₂ : Prop
P₂ = Pvar 2

P₃ : Prop
P₃ = Pvar 3

Dec : ∀ {a} (P : Set a) → Set _
Dec P = Either P (¬ P)

disjunction-comm : ∀ A B → Dec (∅ , A ∨ B ∣ ∅ ⊢ B ∨ A ∙ R ∈LJf)
disjunction-comm A B = isProvable (∅ , A ∨ B ∣ ∅ ⊢ B ∨ A ∙ R)
disjunction-comm? = disjunction-comm P₁ P₂
disjunction-comm?-LJ = mapEither translate (λ x → x) disjunction-comm?

lem : ∀ A → Dec (∅ ∣ ∅ ⊢ A ∨ (A ⟶ ⊥) ∙ R ∈LJf)
lem A = isProvable (∅  ∣ ∅ ⊢ A ∨ (A ⟶ ⊥) ∙ R)
lem? = lem P₁
lem?-false : ¬ (∅ ∣ ∅ ⊢ P₁ ∨ (P₁ ⟶ ⊥) ∙ R ∈LJf)
lem?-false =
  λ { (∨R₁ (initSearch _ ()))
    ; (∨R₂ (→R (id-f⟨ (initSearch _ (continueSearch ())))))
    ; (∨R₂ (initSearch () _))
    ; (initSearch () _)
    }
neg_  : Prop → Prop
neg_ φ = φ ⟶ ⊥

unsatisfiable-cnf : ∀ x y z → Prop
unsatisfiable-cnf x y z = ((((((c₁ ∧ c₂) ∧ c₃) ∧ c₄) ∧ c₅) ∧ c₆) ∧ c₇) ∧ c₈
  where
  c₁ = (x ∨ y) ∨ z
  c₂ = (x ∨ y) ∨ (neg z)
  c₃ = (x ∨ (neg y)) ∨ z
  c₄ = (x ∨ (neg y)) ∨ (neg z)
  c₅ = ((neg x) ∨ y) ∨ z
  c₆ = ((neg x) ∨ y) ∨ (neg z)
  c₇ = ((neg x) ∨ (neg y)) ∨ z
  c₈ = ((neg x) ∨ (neg y)) ∨ (neg z)

¬¬¬unstatisfiable-cnf =
    (isProvable (∅ ∣ ∅ ⊢ neg (neg (neg (unsatisfiable-cnf P₁ P₂ P₃))) ∙ R))
