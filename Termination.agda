module Termination where

open import Agda.Primitive using (lzero)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary.Negation.Core using (¬_) public
open import Induction.WellFounded using (Acc; acc; WellFounded; module Inverse-image)
open import Data.Unit.Base using (tt)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; _≤_; z≤n; s≤s; s<s)
open import Data.Nat.Properties
  using ( module ≤-Reasoning
        ; ≤-reflexive; ≤-trans
        ; m<m+n; m<n+m; m≤m+n; m≤n+m; +-assoc; *-comm
        ; *-monoˡ-≤; *-monoʳ-≤; +-monoʳ-≤; +-monoʳ-<; +-monoˡ-<; +-mono-<-≤
        )
open import Data.Nat.Tactic.RingSolver using (solve; solve-∀) public
open import Data.Product using (_×_) renaming (_,_ to pair)
open import LJf
  using ( SequentWithCursorAndMode; _∣_⊢_∙_; Mode; S; R; derivationFor; _,,_
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
open import Prop using (Prop; Pvar; ⊤; ⊥; _∧_; _∨_; _⟶_; prop-dec-≡; dec-∈)
open import Prelude
  using ( Either; left; right
        ; List; ∅; _,_
        ; _<×<_; lexical-fst; lexical-snd; ℕ×ℕ-wf
        )

------------------------------------------------------------------------
-- Define the measure on sequents used for the well-founded induction --
------------------------------------------------------------------------

-- Define the weight of a proposition.
-- A. S. Troelstra and H. Schwichtenberg. Basic Proof Theory. Cambridge Tracts in Theoretical Computer Science. Cambridge University Press, 2 edition, 2000.
pweight : Prop → ℕ
pweight (Pvar _) = 2 
pweight ⊤        = 2 
pweight ⊥        = 2  
pweight (A ∧ B)  = pweight A * (1 + pweight B)
pweight (A ∨ B)  = 1 + pweight A + pweight B
pweight (A ⟶ B)  = 1 + (pweight A * pweight B)

cweight : List Prop → ℕ
cweight ∅ = 0
cweight (xs , x) = cweight xs + pweight x

length : ∀ {A : Set} → List A → ℕ
length ∅ = 0
length (xs , _) = suc (length xs)

mweight : Mode → ℕ
mweight S = 0
mweight R = 1

sweight : SequentWithCursorAndMode → ℕ × ℕ
sweight (Γ ∣ Δ ⊢ C ∙ m) =
  pair
    (pweight C + cweight Γ + cweight Δ + mweight m)
    (length Γ)

infix 3 _≺_
_≺_ : Rel SequentWithCursorAndMode lzero
s₁ ≺ s₂ = sweight s₁ <×< sweight s₂

≺-wf : WellFounded _≺_
≺-wf = Inverse-image.wellFounded sweight ℕ×ℕ-wf

---------------------------------------------------------------
-- Establish lemmas relating to the measure, because we will --
-- need to prove a lot of innequalities                      --
---------------------------------------------------------------

-- We observe first that pweight(φ) ≥ 2 ∀φ ∈ Prop.
2≤pw : ∀ φ → 2 ≤ pweight φ
2≤pw (Pvar _) = s≤s (s≤s z≤n)
2≤pw ⊤ = s≤s (s≤s z≤n)
2≤pw ⊥ = s≤s (s≤s z≤n)
2≤pw (A ∧ B) =
  begin
    2                                         ≤⟨ 2≤pw A ⟩
    pweight A                                 ≤⟨ m≤m+n (pweight A) (pweight B * pweight A) ⟩
    pweight A + pweight B * pweight A         ≡⟨⟩
    suc (pweight B) * pweight A               ≡⟨ *-comm (suc (pweight B)) (pweight A) ⟩
    pweight A * suc (pweight B)
  ∎
  where open ≤-Reasoning
2≤pw (A ∨ B) =
  begin
    2                                         ≤⟨ 2≤pw B ⟩
    pweight B                                 ≤⟨ m≤n+m (pweight B) (suc (pweight A)) ⟩
    suc (pweight A) + pweight B
  ∎
  where open ≤-Reasoning
2≤pw (A ⟶ B) =
  begin
    2                                     ≤⟨ s≤s (s≤s z≤n) ⟩
    2 * 2                                 ≤⟨ (*-monoʳ-≤ 2 (2≤pw B)) ⟩
    2 * pweight B                         ≤⟨ *-monoˡ-≤ (pweight B) (2≤pw A) ⟩
    pweight A * pweight B                 ≤⟨ m≤n+m (pweight A * pweight B) 1 ⟩
    1 + pweight A * pweight B             ≡⟨⟩
    suc (pweight A * pweight B)
  ∎
  where open ≤-Reasoning

-- We observe that pweight(A) < pweight(B) * peight(A)  ∀A,B ∈ Prop.
wA<wA*wB : ∀ A B → pweight A < pweight A * pweight B
wA<wA*wB A B = p (pweight A) (pweight B) (2≤pw A) (2≤pw B)
  where
  open ≤-Reasoning
  p : ∀ wA wB → 2 ≤ wA → 2 ≤ wB → wA < wA * wB
  p zero _            () 2≤wB
  p _    zero       _ ()
  p _    (suc zero) _ (s≤s ())
  p (suc n) (suc (suc m)) 2≤wA 2≤wB =
    begin-strict
      suc n                             <⟨ m<m+n (suc n) (s≤s z≤n) ⟩
      suc n + (suc n * suc m)           ≡⟨ solve (∅ , n , m) ⟩
      suc n * suc (suc m)
    ∎

-- It follows also that 0 < pweight(A) * pweight(B).
0<wA*wB : ∀ A B → 0 < pweight A * pweight B
0<wA*wB A B =
  begin-strict
    0                          <⟨ s≤s z≤n ⟩
    2                          ≤⟨ 2≤pw A ⟩
    pweight A                  <⟨ wA<wA*wB A B ⟩
    pweight A * pweight B
  ∎
  where open ≤-Reasoning

-----------------------------------------------------------------------------
-- Now we prove that for all inference rules, each premise is smaller than --
-- the its conclusion according to the measure                             --
-----------------------------------------------------------------------------

f⟨-wf : ∀ Γ Δ x C m
        → (Γ ∣ x ,, Δ ⊢ C ∙ m) ≺ (Γ , x ∣ Δ ⊢ C ∙ m)
f⟨-wf Γ Δ x C m = lexical-snd
  (lemm (cweight Γ) (cweight Δ) (pweight x) (pweight C) (mweight m))
  (s<s (≤-reflexive refl))
  where
  lemm : ∀ wΓ wΔ wx wC m
       → wC + wΓ + (wΔ + wx) + m ≡ wC + (wΓ + wx) + wΔ + m
  lemm = solve-∀

∧R-wf₁ : ∀ Γ A B
       → Γ ∣ ∅ ⊢ A ∙ R ≺ ∅ ∣ Γ ⊢ A ∧ B ∙ R
∧R-wf₁ Γ A B =
  lexical-fst (p (pweight A) (pweight B) (cweight Γ) (0<wA*wB A B))
  where
  open ≤-Reasoning
  p : ∀ wA wB wΓ → 0 < wA * wB → wA + wΓ + 0 + 1 < wA * suc wB + 0 + wΓ + 1
  p wA wB wΓ 0<wAB =
    begin-strict
      wA + wΓ + 0 + 1                <⟨ m<n+m (wA + wΓ + 0 + 1) 0<wAB ⟩
      wA * wB + (wA + wΓ + 0 + 1)    ≡⟨ solve (∅ , wΓ , wA , wB) ⟩
      wA * suc wB + 0 + wΓ + 1
    ∎


∧R-wf₂ : ∀ Γ A B
         → Γ ∣ ∅ ⊢ B ∙ R ≺ ∅ ∣ Γ ⊢ A ∧ B ∙ R
∧R-wf₂ Γ A B =
  lexical-fst (p (pweight A) (pweight B) (cweight Γ) (wA<wA*wB B A))
  where
  p : ∀ wA wB wΓ → wB < wB * wA → wB + wΓ + 0 + 1 < wA * suc wB + 0 + wΓ + 1
  p wA wB wΓ wB<wB*wA =
    begin-strict
      wB + wΓ + 0 + 1            ≡⟨ solve (∅ , wΓ , wB) ⟩
      wB + wΓ + 1                ≡⟨ +-assoc wB wΓ 1 ⟩
      wB + (wΓ + 1)              <⟨ +-monoˡ-< (wΓ + 1) wB<wB*wA ⟩
      wB * wA + (wΓ + 1)         ≤⟨ m≤n+m (wB * wA + (wΓ + 1)) wA ⟩
      wA + (wB * wA + (wΓ + 1))  ≡⟨ solve (∅ , wΓ , wA , wB) ⟩
      wA * suc wB + 0 + wΓ + 1
    ∎
    where open ≤-Reasoning

∨R₁-wf : ∀ Γ A B
       → Γ ∣ ∅ ⊢ A ∙ R ≺ ∅ ∣ Γ ⊢ A ∨ B ∙ R
∨R₁-wf Γ A B = lexical-fst (p (pweight A) (pweight B) (cweight Γ))
  where
  open ≤-Reasoning
  p : ∀ wA wB wΓ → wA + wΓ + 0 + 1 < suc (wA + wB + 0 + wΓ + 1)
  p wA wB wΓ =
    begin-strict
      wA + wΓ + 0 + 1            ≡⟨ solve (∅ , wΓ , wA) ⟩
      wA + wΓ + 1                ≤⟨ m≤m+n (wA + wΓ + 1) wB ⟩
      wA + wΓ + 1 + wB           <⟨ m<n+m (wA + wΓ + 1 + wB) (s≤s (z≤n {0})) ⟩
      1 + (wA + wΓ + 1 + wB)     ≡⟨ solve (∅ , wΓ , wA , wB) ⟩
      suc (wA + wB + 0 + wΓ + 1)
    ∎

∨R₂-wf : ∀ Γ A B
       → Γ ∣ ∅ ⊢ B ∙ R ≺ ∅ ∣ Γ ⊢ A ∨ B ∙ R
∨R₂-wf Γ A B = lexical-fst (p (pweight A) (pweight B) (cweight Γ))
  where
  p : ∀ wA wB wΓ → wB + wΓ + 0 + 1 < suc (wA + wB + 0 + wΓ + 1)
  p wA wB wΓ =
    begin-strict
      wB + wΓ + 0 + 1            ≡⟨ solve (∅ , wΓ , wB) ⟩
      wB + wΓ + 1                ≤⟨ m≤m+n (wB + wΓ + 1) wA ⟩
      wB + wΓ + 1 + wA           <⟨ m<n+m (wB + wΓ + 1 + wA) (s≤s (z≤n {0})) ⟩
      1 + (wB + wΓ + 1 + wA)     ≡⟨ solve (∅ , wΓ , wA , wB) ⟩
      suc (wA + wB + 0 + wΓ + 1)
    ∎
    where open ≤-Reasoning

→R-wf : ∀ Γ A B
      → Γ , A ∣ ∅ ⊢ B ∙ R ≺ ∅ ∣ Γ ⊢ A ⟶ B ∙ R
→R-wf Γ A B =
  lexical-fst (p (pweight A) (pweight B) (cweight Γ) (2≤pw A) (2≤pw B))
  where
  p : ∀ wA wB wΓ
    → 2 ≤ wA
    → 2 ≤ wB
    → wB + (wΓ + wA) + 0 + 1 < suc (wA * wB + 0 + wΓ + 1)
  p wA wB wΓ h₁ h₂ =
    begin-strict
      wB + (wΓ + wA) + 0 + 1    ≡⟨ solve (∅ , wΓ , wA , wB) ⟩
      wB + (wΓ + wA) + 1        ≡⟨ solve (∅ , wΓ , wA , wB) ⟩
      (1 + wΓ) + (wA + wB)      ≤⟨ +-monoʳ-≤ (1 + wΓ) (lemm wA wB h₁ h₂) ⟩
      (1 + wΓ) + (wA * wB)      ≡⟨ solve (∅ , wΓ , wA , wB) ⟩
      wA * wB + 0 + wΓ + 1      <⟨ s≤s (≤-reflexive refl) ⟩
      suc (wA * wB + 0 + wΓ + 1)
    ∎
    where
    open ≤-Reasoning
    lemm : ∀ a b → 2 ≤ a → 2 ≤ b → a + b ≤ a * b
    lemm zero _ () _
    lemm _ zero _ ()
    lemm (suc zero) _ (s≤s ()) _
    lemm _ (suc zero) _ (s≤s ())
    lemm (suc (suc a)) (suc (suc b)) _ _ =
      begin
        suc (suc a) + suc (suc b)                    ≡⟨ solve (∅ , a , b) ⟩
        4 + a + b                                    ≤⟨ m≤m+n (4 + a + b) (a + b + a * b) ⟩
        (4 + a + b) + (a + b + a * b)                ≡⟨ solve (∅ , a , b) ⟩
        suc (suc a) * suc (suc b)
      ∎

⊤L-wf : ∀ Γ Δ C
      → Γ ∣ Δ ⊢ C ∙ R ≺ Γ , ⊤ ∣ Δ ⊢ C ∙ R
⊤L-wf Γ Δ C = lexical-fst (p (cweight Γ) (cweight Δ) (pweight C))
  where
  p : ∀ wΓ wΔ wC → wC + wΓ + wΔ + 1 < wC + (wΓ + 2) + wΔ + 1
  p wΓ wΔ wC =
    begin-strict
      wC + wΓ + wΔ + 1        <⟨ m<m+n (wC + wΓ + wΔ + 1) (s≤s z≤n) ⟩
      wC + wΓ + wΔ + 1 + 2    ≡⟨ solve (∅ , wΓ , wΔ , wC) ⟩
      wC + (wΓ + 2) + wΔ + 1
    ∎
    where open ≤-Reasoning

∧L-wf : ∀ Γ Δ A B C
      → Γ , A , B ∣ Δ ⊢ C ∙ R ≺ Γ , A ∧ B ∣ Δ ⊢ C ∙ R
∧L-wf Γ Δ A B C =
  lexical-fst (p (cweight Γ) (cweight Δ) (pweight A) (pweight B) (pweight C) (wA<wA*wB B A))
  where
  p : ∀ wΓ wΔ wA wB wC
    → wB < wB * wA
    → wC + (wΓ + wA + wB) + wΔ + 1 < wC + (wΓ + wA * suc (wB)) + wΔ + 1
  p wΓ wΔ wA wB wC wB<wBA =
    begin-strict
      wC + (wΓ + wA + wB) + wΔ + 1      ≡⟨ solve (∅ , wΓ , wΔ , wA , wB , wC) ⟩
      wB + (wA + wC + wΓ + wΔ + 1)      <⟨ +-monoˡ-< (wA + wC + wΓ + wΔ + 1) wB<wBA ⟩
      wB * wA + (wA + wC + wΓ + wΔ + 1) ≡⟨ solve (∅ , wΓ , wΔ , wA , wB , wC) ⟩
      wC + (wΓ + wA * suc wB) + wΔ + 1
    ∎
    where open ≤-Reasoning

∨L-wf₁ : ∀ Γ Δ A B C
       → Γ , A ∣ Δ ⊢ C ∙ R ≺ Γ , A ∨ B ∣ Δ ⊢ C ∙ R
∨L-wf₁ Γ Δ A B C =
  lexical-fst (p
    (cweight Γ)
    (cweight Δ)
    (pweight A)
    (pweight B)
    (pweight C)
    (cweight (Γ , A))
    refl
  )
  where 
  p : ∀ wΓ wΔ wA wB wC wΓA
    → wΓA ≡ wΓ + wA
    → wC + wΓA + wΔ + 1 < wC + (wΓ + suc (wA + wB)) + wΔ + 1
  p wΓ wΔ wA wB wC wΓA h =
    begin-strict
      wC + wΓA + wΔ + 1                ≡⟨ solve (∅ , wΓA , wΔ , wC) ⟩
      wC + wΓA + (wΔ + 1)              ≡⟨ cong (λ x → wC + x + (wΔ + 1)) h ⟩
      wC + (wΓ + wA) + (wΔ + 1)        ≡⟨ solve (∅ , wΓ , wΔ , wA , wC) ⟩
      wC + wΓ + wΔ + wA + 1            <⟨ m<m+n (wC + wΓ + wΔ + wA + 1) (s≤s z≤n) ⟩
      (wC + wΓ + wΔ + wA + 1) + suc wB ≡⟨ solve (∅ , wΓ , wΔ , wA , wB , wC) ⟩
      wC + (wΓ + suc (wA + wB)) + wΔ + 1
    ∎
    where open ≤-Reasoning

∨L-wf₂ : ∀ Γ Δ A B C
       → Γ , B ∣ Δ ⊢ C ∙ R ≺ Γ , A ∨ B ∣ Δ ⊢ C ∙ R
∨L-wf₂ Γ Δ A B C =
  lexical-fst (p
    (cweight Γ)
    (cweight Δ)
    (pweight A)
    (pweight B)
    (pweight C)
    (cweight (Γ , B))
    refl
  )
  where 
  p : ∀ wΓ wΔ wA wB wC wΓB
    → wΓB ≡ wΓ + wB
    → wC + wΓB + wΔ + 1 < wC + (wΓ + suc (wA + wB)) + wΔ + 1
  p wΓ wΔ wA wB wC wΓB h =
    begin-strict
      wC + wΓB + wΔ + 1                ≡⟨ cong (λ x → wC + x + wΔ + 1) h ⟩
      wC + (wΓ + wB) + wΔ + 1          ≡⟨ solve (∅ , wΓ , wΔ , wB , wC) ⟩
      wC + wΓ + wΔ + wB + 1            <⟨ m<m+n (wC + wΓ + wΔ + wB + 1) (s≤s z≤n) ⟩
      (wC + wΓ + wΔ + wB + 1) + suc wA ≡⟨ solve (∅ , wΓ , wΔ , wA , wB , wC) ⟩
      wC + (wΓ + suc (wA + wB)) + wΔ + 1
    ∎
    where open ≤-Reasoning

P→L-wf : ∀ Γ Δ n B C m
       → Γ , B ∣ Δ ⊢ C ∙ R ≺ Γ , Pvar n ⟶ B ∣ Δ ⊢ C ∙ m
P→L-wf Γ Δ _ B C m =
  lexical-fst (p
    (cweight Γ)
    (cweight Δ)
    (pweight B)
    (pweight C)
    (mweight m)
    (≤-trans (s≤s z≤n) (2≤pw B))
  )
  where
  p : ∀ wΓ wΔ wB wC m
    → 1 ≤ wB 
    → wC + (wΓ + wB) + wΔ + 1 < wC + (wΓ + suc (wB + (wB + 0))) + wΔ + m
  p wΓ wΔ wB wC m h =
    begin-strict
      wC + (wΓ + wB) + wΔ + 1            ≡⟨ solve (∅ , wΓ , wΔ , wB , wC) ⟩
      (wC + wΓ + wB + wΔ) + 1            <⟨ +-monoʳ-< (wC + wΓ + wB + wΔ) (s≤s h) ⟩
      (wC + wΓ + wB + wΔ) + suc wB       ≤⟨ m≤m+n ((wC + wΓ + wB + wΔ) + suc wB) m ⟩
      ((wC + wΓ + wB + wΔ) + suc wB) + m ≡⟨ solve (∅ , wΓ , wΔ , wB , wC) ⟩
      wC + (wΓ + suc (wB + (wB + 0))) + wΔ + m
    ∎
    where open ≤-Reasoning

⊤→L-wf : ∀ Γ Δ B C
       → Γ , B ∣ Δ ⊢ C ∙ R ≺ Γ , ⊤ ⟶ B ∣ Δ ⊢ C ∙ R
⊤→L-wf Γ Δ B C =
  lexical-fst (p
    (cweight Γ)
    (cweight Δ)
    (pweight B)
    (pweight C)
    (cweight (Γ , B))
    refl
  )
  where
  p : ∀ wΓ wΔ wB wC wΓB
    → wΓB ≡ wΓ + wB
    → wC + wΓB + wΔ + 1 < wC + (wΓ + suc (wB + (wB + 0))) + wΔ + 1
  p wΓ wΔ wB wC wΓB h =
    begin-strict
      wC + wΓB + wΔ + 1                ≡⟨ cong (λ x → wC + x + wΔ + 1) h ⟩
      wC + (wΓ + wB) + wΔ + 1          ≡⟨ solve (∅ , wΓ , wΔ , wB , wC) ⟩
      wC + wΓ + wB + wΔ + 1            <⟨ m<m+n (wC + wΓ + wB + wΔ + 1) (s≤s z≤n) ⟩
      (wC + wΓ + wB + wΔ + 1) + suc wB ≡⟨ solve (∅ , wΓ , wΔ , wB , wC) ⟩
      wC + (wΓ + suc (wB + (wB + 0))) + wΔ + 1
    ∎
    where open ≤-Reasoning

⊥→L-wf : ∀ Γ Δ B C
       → Γ ∣ Δ ⊢ C ∙ R ≺ Γ , ⊥ ⟶ B ∣ Δ ⊢ C ∙ R
⊥→L-wf Γ Δ B C =
  lexical-fst (p
    (cweight Γ)
    (cweight Δ)
    (pweight B)
    (pweight C)
  )
  where
  p : ∀ wΓ wΔ wB wC
    →  wC + wΓ + wΔ + 1 < wC + (wΓ + suc (wB + (wB + 0))) + wΔ + 1
  p wΓ wΔ wB wC =
    begin-strict
      wC + wΓ + wΔ + 1                   <⟨ m<m+n (wC + wΓ + wΔ + 1) (s≤s z≤n) ⟩
      (wC + wΓ + wΔ + 1) + suc wB        ≤⟨ m≤m+n (((wC + wΓ + wΔ + 1) + suc wB)) wB ⟩
      ((wC + wΓ + wΔ + 1) + suc wB) + wB ≡⟨ solve (∅ , wΓ , wΔ , wB , wC) ⟩
      wC + (wΓ + suc (wB + (wB + 0))) + wΔ + 1
    ∎
    where open ≤-Reasoning

∧→L-wf : ∀ Γ Δ A₁ A₂ B C
       → Γ , A₁ ⟶ (A₂ ⟶ B) ∣ Δ ⊢ C ∙ R ≺ Γ , A₁ ∧ A₂ ⟶ B ∣ Δ ⊢ C ∙ R
∧→L-wf Γ Δ A₁ A₂ B C =
  lexical-fst (+-mono-<-≤ (p
    (cweight Γ)
    (cweight Δ)
    (pweight A₁)
    (pweight A₂)
    (pweight B)
    (pweight C)
    (wA<wA*wB A₁ B)
  ) (s≤s z≤n))
  where
  open ≤-Reasoning
  p : ∀ wΓ wΔ wA₁ wA₂ wB wC
    → wA₁ < wA₁ * wB
    →    wC + (wΓ + suc (wA₁ * suc (wA₂ * wB))) + wΔ
      <  wC + (wΓ + suc (wA₁ * suc (wA₂) * wB)) + wΔ
  p wΓ wΔ wA₁ wA₂ wB wC h = 
    begin-strict
      wC + (wΓ + suc (wA₁ * suc (wA₂ * wB))) + wΔ             ≡⟨ solve vs ⟩
      (wΓ + wΔ + wC + 1 + wA₁ * wA₂ * wB) + wA₁               <⟨ +-monoʳ-< lhs h ⟩
      (wΓ + wΔ + wC + 1 + wA₁ * wA₂ * wB) + (wA₁ * wB)        ≡⟨ solve vs ⟩
      wC + (wΓ + suc (wA₁ * suc wA₂ * wB)) + wΔ
    ∎
    where
    vs = ∅ , wΓ , wΔ , wA₁ , wA₂ , wB , wC
    lhs = wΓ + wΔ + wC + 1 + wA₁ * wA₂ * wB

∨→L-wf : ∀ Γ Δ A₁ A₂ B C
       → Γ , A₁ ⟶ B , A₂ ⟶ B ∣ Δ ⊢ C ∙ R ≺ Γ , A₁ ∨ A₂ ⟶ B ∣ Δ ⊢ C ∙ R
∨→L-wf Γ Δ A₁ A₂ B C =
  lexical-fst (+-mono-<-≤ (p
    (cweight Γ)
    (cweight Δ)
    (pweight A₁)
    (pweight A₂)
    (pweight B)
    (pweight C)
    (2≤pw B)
  ) (s≤s z≤n))
  where
  open ≤-Reasoning
  p : ∀ wΓ wΔ wA₁ wA₂ wB wC
    → 2 ≤ wB
    →  wC + (wΓ + suc (wA₁ * wB) + suc (wA₂ * wB)) + wΔ
       < wC + (wΓ + suc (wB + (wA₁ + wA₂) * wB)) + wΔ
  p wΓ wΔ wA₁ wA₂ wB wC h =
    begin-strict
      wC + (wΓ + suc (wA₁ * wB) + suc (wA₂ * wB)) + wΔ   ≡⟨ solve vs ⟩
      (wC + wΓ + wΔ + wA₁ * wB + wA₂ * wB) + 2           ≤⟨ +-monoʳ-≤ lhs h ⟩
      (wC + wΓ + wΔ + wA₁ * wB + wA₂ * wB) + wB          <⟨ s≤s (≤-reflexive refl) ⟩
      suc ((wC + wΓ + wΔ + wA₁ * wB + wA₂ * wB) + wB)    ≡⟨ solve vs ⟩
      wC + (wΓ + suc (wB + (wA₁ + wA₂) * wB)) + wΔ
    ∎
    where
    vs = ∅ , wΓ , wΔ , wA₁ , wA₂ , wB , wC
    lhs = wC + wΓ + wΔ + wA₁ * wB + wA₂ * wB

→→L-wf₁ : ∀ Γ Δ A₁ A₂ B C
        → Γ , A₂ ⟶ B , A₁ ∣ Δ ⊢ A₂ ∙ R ≺ Γ , (A₁ ⟶ A₂) ⟶ B ∣ Δ ⊢ C ∙ R
→→L-wf₁ Γ Δ A₁ A₂ B C =
  lexical-fst (+-mono-<-≤ (p
    (cweight Γ)
    (cweight Δ)
    (pweight A₁)
    (pweight A₂)
    (pweight B)
    (pweight C)
    (2≤pw A₁)
    (2≤pw A₂)
    (2≤pw B)
    (2≤pw C)
  ) (s≤s z≤n))
  where
  open ≤-Reasoning
  p : ∀ wΓ wΔ wA₁ wA₂ wB wC
    → 2 ≤ wA₁
    → 2 ≤ wA₂
    → 2 ≤ wB
    → 2 ≤ wC
    → wA₂ + (wΓ + suc (wA₂ * wB) + wA₁) + wΔ
      < wC + (wΓ + suc (wB + wA₁ * wA₂ * wB)) + wΔ
  p wΓ wΔ wA₁ wA₂ wB wC h₁ h₂ h₃ h₄ =
    begin-strict
      wA₂ + (wΓ + suc (wA₂ * wB) + wA₁) + wΔ
        ≡⟨ solve vs ⟩
      (1 + wΓ + wΔ) + (wA₁ + wA₂ + (wA₂ * wB))
        <⟨ +-monoʳ-< lhs (lemm wA₁ wA₂ wB wC h₁ h₂ h₃ h₄) ⟩
      (1 + wΓ + wΔ) + (wC  + wB + (wA₁ * wA₂ * wB))
        ≡⟨ solve vs ⟩
      wC + (wΓ + suc (wB + wA₁ * wA₂ * wB)) + wΔ
    ∎
    where
    vs = ∅ , wΓ , wΔ , wA₁ , wA₂ , wB , wC

    lhs = 1 + wΓ + wΔ

    lemm : ∀ wA₁ wA₂ wB wC
         → 2 ≤ wA₁
         → 2 ≤ wA₂
         → 2 ≤ wB
         → 2 ≤ wC
         → wA₁ + wA₂ + (wA₂ * wB) < wC  + wB + (wA₁ * wA₂ * wB)
    lemm zero _ _ _ () _ _ _
    lemm _ zero _ _ _ () _ _
    lemm _ _ zero _ _ _ () _
    lemm _ _ _ zero _ _ _ ()
    lemm (suc zero) _ _ _ (s≤s ()) _ _ _
    lemm _ (suc zero) _ _ _ (s≤s ()) _ _
    lemm _ _ (suc zero) _ _ _ (s≤s ()) _
    lemm _ _ _ (suc zero) _ _ _ (s≤s ())
    lemm (suc (suc wA₁)) (suc wA₂) (suc wB) wC _ _ _ h₄ = 
      begin-strict
        (suc (suc wA₁)) + suc wA₂ + (suc wA₂ * suc wB)
          ≡⟨ solve (∅ , wA₁ , wA₂ , wB) ⟩
        1  + (3 + wA₂ + wA₂ + wB + wA₂ * wB + wA₁)
          <⟨ +-monoˡ-< (3 + wA₂ + wA₂ + wB + wA₂ * wB + wA₁) h₄ ⟩
        wC + (3 + wA₂ + wA₂ + wB + wA₂ * wB + wA₁)
          ≤⟨ m≤m+n
             ((wC + (3 + wA₂ + wA₂ + wB + wA₂ * wB + wA₁)))
             ((wA₁ * wA₂ + wB * (1 + (wA₁ + 1) * (wA₂ + 1))))
           ⟩
        (wC + (3 + wA₂ + wA₂ + wB + wA₂ * wB + wA₁))
          + (wA₁ * wA₂ + wB * (1 + (wA₁ + 1) * (wA₂ + 1)))
          ≡⟨ solve (∅ , wA₁ , wA₂ , wB) ⟩
        wC  + suc wB + (suc (suc wA₁)) * suc wA₂ * suc wB
      ∎

→→L-wf₂ : ∀ Γ Δ A₁ A₂ B C
        → Γ , B ∣ Δ ⊢ C ∙ R ≺ Γ , (A₁ ⟶ A₂) ⟶ B ∣ Δ ⊢ C ∙ R
→→L-wf₂ Γ Δ A₁ A₂ B C =
  lexical-fst (+-mono-<-≤ (p
    (cweight Γ)
    (cweight Δ)
    (pweight A₁)
    (pweight A₂)
    (pweight B)
    (pweight C)
  ) (s≤s z≤n))
  where
  open ≤-Reasoning
  p : ∀ wΓ wΔ wA₁ wA₂ wB wC
    → wC + (wΓ + wB) + wΔ
      < wC + (wΓ + suc (wB + wA₁ * wA₂ * wB)) + wΔ
  p wΓ wΔ wA₁ wA₂ wB wC =
    begin-strict
      wC + (wΓ + wB) + wΔ
        ≡⟨ solve (∅ , wΓ , wΔ , wB , wC) ⟩
      (wΓ + wΔ + wB + wC)
        <⟨ m<m+n (wΓ + wΔ + wB + wC) (s≤s z≤n) ⟩
      (wΓ + wΔ + wB + wC) + 1
        ≤⟨ m≤m+n ((wΓ + wΔ + wB + wC) + 1) (wA₁ * wA₂ * wB) ⟩
      ((wΓ + wΔ + wB + wC) + 1) + wA₁ * wA₂ * wB
        ≡⟨ solve (∅ , wΓ , wΔ , wA₁ , wA₂ , wB , wC) ⟩
      wC + (wΓ + suc (wB + wA₁ * wA₂ * wB)) + wΔ
    ∎

initSearch-wf : ∀ Γ C → Γ ∣ ∅ ⊢ C ∙ S ≺ ∅ ∣ Γ ⊢ C ∙ R
initSearch-wf Γ C = lexical-fst (lemm (cweight Γ) (pweight C))
  where
  open ≤-Reasoning
  lemm : ∀ wΓ wC → wC + wΓ + 0 + 0 < wC + 0 + wΓ + 1
  lemm wΓ wC =
    begin-strict
      wC + wΓ + 0 + 0           ≡⟨ solve (∅ , wΓ , wC) ⟩
      wC + wΓ                   <⟨ m<m+n (wC + wΓ) (s≤s z≤n) ⟩
      (wC + wΓ) + 1             ≡⟨ solve (∅ , wΓ , wC) ⟩
      wC + 0 + wΓ + 1
    ∎

continueSearch-wf₁ : ∀ Γ Δ A C m → Γ ∣ A ,, Δ ⊢ C ∙ m ≺ Γ , A ∣ Δ ⊢ C ∙ m
continueSearch-wf₁ Γ Δ A C m =
  lexical-snd
    (lemm
      (cweight Γ)
      (cweight Δ)
      (pweight A)
      (pweight C)
      (mweight m)
    )
    (s≤s (≤-reflexive refl))
  where
  lemm : ∀ wΓ wΔ wA wC wm
       → wC + wΓ + (wΔ + wA) + wm ≡ wC + (wΓ + wA) + wΔ + wm
  lemm = solve-∀

continueSearch-wf₂ : ∀ Γ Δ A B C → Γ , B ∣ Δ ⊢ C ∙ R ≺ Γ , A ⟶ B ∣ Δ ⊢ C ∙ S
continueSearch-wf₂ Γ Δ A B C =
  lexical-fst
    (lemm
      (cweight Γ)
      (cweight Δ)
      (pweight A)
      (pweight B)
      (pweight C)
      (wA<wA*wB B A)
    )
  where
  open ≤-Reasoning
  lemm : ∀ wΓ wΔ wA wB wC
        → wB < wB * wA
        → wC + (wΓ + wB) + wΔ + 1 < wC + (wΓ + suc (wA * wB)) + wΔ + 0
  lemm wΓ wΔ wA wB wC h =
    begin-strict
      wC + (wΓ + wB) + wΔ + 1              ≡⟨ solve (∅ , wΓ , wΔ , wA , wB , wC) ⟩
      (wC + wΓ + wΔ + 1) + wB              <⟨ +-monoʳ-< ((wC + wΓ + wΔ + 1)) h ⟩
      (wC + wΓ + wΔ + 1) + (wB * wA)       ≡⟨ solve (∅ , wΓ , wΔ , wA , wB , wC) ⟩
      wC + (wΓ + suc (wA * wB)) + wΔ + 0 ∎

----------------------------------------------------------------------------
-- Now we can implement the search procedure using well-founded induction --
----------------------------------------------------------------------------

-- `ps` is `isProvable'` in the thesis.
ps : (s : SequentWithCursorAndMode)
     → Acc _≺_ s
     → Either (derivationFor s) (¬ derivationFor s)
-- This is the base-case where we fail.
-- The cursor has reached the end in search mode.
ps (∅ ∣ _ ⊢ _ ∙ S) _      = right λ()

ps (∅ ∣ _ ⊢ ⊤ ∙ R) _      = left ⊤R

-- If the cursor reaches the end in reduce mode and
-- we cannot reduce the succedent we
-- rewind and change to search mode.
ps (∅ ∣ Γ ⊢ ⊥ ∙ R) (acc rs)
 with ps (Γ ∣ ∅ ⊢ ⊥ ∙ S) (rs (initSearch-wf Γ ⊥))
... | left  h = left (initSearch tt h)
... | right h = right λ{ (initSearch _ s) → h s }
ps (∅ ∣ Γ ⊢ Pvar n ∙ R) (acc rs)
 with ps (Γ ∣ ∅ ⊢ Pvar n ∙ S) (rs (initSearch-wf Γ (Pvar n)))
... | left  h = left (initSearch tt h)
... | right h = right λ{ (initSearch _ s) → h s }

-- If the cursor reached the end in reduce mode
-- and we can reduce the succedent then we do that
-- and rewind the cursor
ps (∅ ∣ Γ ⊢ (A ∧ B) ∙ R) (acc rs)
  with ps (Γ ∣ ∅ ⊢ A ∙ R) (rs (∧R-wf₁ Γ A B))
     | ps (Γ ∣ ∅ ⊢ B ∙ R) (rs (∧R-wf₂ Γ A B))
...  | left  h | left  t = left (∧R h t)
...  | right h | _       = right λ{ (∧R x _) → h x}
...  | _       | right h = right λ{ (∧R _ x) → h x}
ps (∅ ∣ Γ ⊢ (A ∨ B) ∙ R) (acc rs)
  with ps (Γ ∣ ∅ ⊢ A ∙ R) (rs (∨R₁-wf Γ A B))
     | ps (Γ ∣ ∅ ⊢ B ∙ R) (rs (∨R₂-wf Γ A B))
...  | (left  ⊢A) | _          = left (∨R₁ ⊢A)
...  | _          | (left  ⊢B) = left (∨R₂ ⊢B)
...  | (right ⊬A) | (right ⊬B) = right λ{ (∨R₁ ⊢A) → ⊬A ⊢A
                                        ; (∨R₂ ⊢B) → ⊬B ⊢B
                                        }
ps (∅ ∣ Γ ⊢ (A ⟶ B) ∙ R) (acc rs)
 with ps (Γ , A ∣ ∅ ⊢ B ∙ R) (rs (→R-wf Γ A B))
... | left  h = left (→R h)
... | right h = right λ{ (→R x) → h x }

-- Reduce propositions in the context.
ps (Γ , ⊤ ∣ Δ ⊢ C ∙ R) (acc rs)
 with ps (Γ ∣ Δ ⊢ C ∙ R) (rs (⊤L-wf Γ Δ C))
... | left  h = left (⊤L h)
... | right h = right λ{ (⊤L x) → h x }
ps (Γ , ⊥  ∣ _ ⊢ _ ∙ R) _ = left ⊥L
ps (Γ , Pₙ@(Pvar n) ∣ Δ ⊢ C ∙ R) (acc rs)
 with prop-dec-≡ Pₙ C
... | left  refl = left id
... | right Pₙ≢C with ps (Γ ∣ Pₙ ,, Δ ⊢ C ∙ R) (rs (f⟨-wf Γ Δ Pₙ C R))
...                 | left  x = left (id-f⟨ x)
...                 | right x = right λ{ id → Pₙ≢C refl
                                       ; (id-f⟨ y) → x y
                                       }
ps (Γ , A ∧ B ∣ Δ ⊢ C ∙ R) (acc rs)
 with ps (Γ , A , B ∣ Δ ⊢ C ∙ R) (rs (∧L-wf Γ Δ A B C))
... | left  x = left (∧L x )
... | right x = right λ{ (∧L y) → x y }
ps (Γ , A ∨ B ∣ Δ ⊢ C ∙ R) (acc rs)
 with ps (Γ , A ∣ Δ ⊢ C ∙ R) (rs (∨L-wf₁ Γ Δ A B C))
    | ps (Γ , B ∣ Δ ⊢ C ∙ R) (rs (∨L-wf₂ Γ Δ A B C))
... | left  A⊢C | left  B⊢C = left (∨L A⊢C B⊢C)
... | right A⊬C | _         = right λ{ (∨L A⊢C _) → A⊬C A⊢C
                                        }
...    | _         | right B⊬C = right λ{ (∨L _ B⊢C) → B⊬C B⊢C
                                        }
ps (Γ , ⊤ ⟶ B ∣ Δ ⊢ C ∙ R) (acc rs)
 with ps (Γ , B ∣ Δ ⊢ C ∙ R) (rs (⊤→L-wf Γ Δ B C))
... | left  h = left (⊤→L h)
... | right h = right λ{ (⊤→L x) → h x }
ps (Γ , ⊥ ⟶ B ∣ Δ ⊢ C ∙ R) (acc rs)
 with ps (Γ ∣ Δ ⊢ C ∙ R) (rs (⊥→L-wf Γ Δ B C))
... | left  h = left (⊥→L h)
... | right h = right λ{ (⊥→L x) → h x }
ps (Γ , A₁ ∧ A₂ ⟶ B ∣ Δ ⊢ C ∙ R) (acc rs)
 with ps (Γ , A₁ ⟶ (A₂ ⟶ B) ∣ Δ ⊢ C ∙ R) (rs (∧→L-wf Γ Δ A₁ A₂ B C))
... | left  h = left (∧→L h)
... | right h = right λ{ (∧→L x) → h x }
ps (Γ , A₁ ∨ A₂ ⟶ B ∣ Δ ⊢ C ∙ R) (acc rs)
 with ps (Γ , A₁ ⟶ B , A₂ ⟶ B ∣ Δ ⊢ C ∙ R) (rs (∨→L-wf Γ Δ A₁ A₂ B C))
...  | left  h = left (∨→L h)
...  | right h = right λ{ (∨→L x) → h x}
ps (Γ , (A₁ ⟶ A₂) ⟶ B ∣ Δ ⊢ C ∙ R) (acc rs)
 with ps (Γ , A₂ ⟶ B , A₁ ∣ Δ ⊢ A₂ ∙ R) (rs (→→L-wf₁ Γ Δ A₁ A₂ B C))
    | ps (Γ , B ∣ Δ ⊢ C ∙ R) (rs (→→L-wf₂ Γ Δ A₁ A₂ B C))
... | left  h | left  t = left (→→L h t)
... | right h | _       = right λ{ (→→L x _) → h x }
... | _       | right h = right λ{ (→→L _ x) → h x }

-- Handle Pₙ → B for reduce resp. search mode.
ps (Γ , Pₙ@(Pvar n) ⟶ B ∣ Δ ⊢ C ∙ R) (acc rs)
 with ps (Γ , B ∣ Δ ⊢ C ∙ R) (rs (P→L-wf Γ Δ n B C R))
    | ps (Γ ∣ Pₙ ⟶ B ,, Δ ⊢ C ∙ R) (rs (continueSearch-wf₁ Γ Δ (Pₙ ⟶ B) C R))
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
ps (Γ , Pₙ@(Pvar n) ⟶ B ∣ Δ ⊢ C ∙ S) (acc rs)
 with ps (Γ , B ∣ Δ ⊢ C ∙ R) (rs (P→L-wf Γ Δ n B C S))
    | ps (Γ ∣ Pₙ ⟶ B ,, Δ ⊢ C ∙ S) (rs (continueSearch-wf₁ Γ Δ (Pₙ ⟶ B) C S))
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
ps (Γ , Pvar n ∣ Δ ⊢ C ∙ S) (acc rs)
 with ps (Γ ∣ Pvar n ,, Δ ⊢ C ∙ S) (rs (f⟨-wf Γ Δ (Pvar n) C S))
... | left  h = left (continueSearch h)
... | right h = right λ{ (continueSearch t) → h t }
ps (Γ , ⊤ ∣ Δ ⊢ C ∙ S) (acc rs)
 with ps (Γ ∣ ⊤ ,, Δ ⊢ C ∙ S) (rs (f⟨-wf Γ Δ ⊤ C S))
... | left  h = left (continueSearch h)
... | right h = right λ{ (continueSearch t) → h t }
ps (Γ , ⊥ ∣ Δ ⊢ C ∙ S) (acc rs)
 with ps (Γ ∣ ⊥ ,, Δ ⊢ C ∙ S) (rs (f⟨-wf Γ Δ ⊥ C S))
... | left  h = left (continueSearch h)
... | right h = right λ{ (continueSearch t) → h t }
ps (Γ , A ∧ B ∣ Δ ⊢ C ∙ S) (acc rs)
 with ps (Γ ∣ A ∧ B ,, Δ ⊢ C ∙ S) (rs (f⟨-wf Γ Δ (A ∧ B) C S))
... | left  h = left (continueSearch h)
... | right h = right λ{ (continueSearch t) → h t }
ps (Γ , A ∨ B ∣ Δ ⊢ C ∙ S) (acc rs)
 with ps (Γ ∣ A ∨ B ,, Δ ⊢ C ∙ S) (rs (f⟨-wf Γ Δ (A ∨ B) C S))
... | left  h = left (continueSearch h)
... | right h = right λ{ (continueSearch t) → h t }
ps (Γ , ⊤ ⟶ B ∣ Δ ⊢ C ∙ S) (acc rs)
 with ps (Γ ∣ ⊤ ⟶ B ,, Δ ⊢ C ∙ S) (rs (f⟨-wf Γ Δ (⊤ ⟶ B) C S))
... | left  h = left (continueSearch h)
... | right h = right λ{ (continueSearch t) → h t }
ps (Γ , ⊥ ⟶ B ∣ Δ ⊢ C ∙ S) (acc rs)
 with ps (Γ ∣ ⊥ ⟶ B ,, Δ ⊢ C ∙ S) (rs (f⟨-wf Γ Δ (⊥ ⟶ B) C S))
... | left  h = left (continueSearch h)
... | right h = right λ{ (continueSearch t) → h t }
ps (Γ , A₁ ∧ A₂ ⟶ B ∣ Δ ⊢ C ∙ S) (acc rs)
 with ps (Γ ∣ A₁ ∧ A₂ ⟶ B ,, Δ ⊢ C ∙ S) (rs (f⟨-wf Γ Δ (A₁ ∧ A₂ ⟶ B) C S))
... | left  h = left (continueSearch h)
... | right h = right λ{ (continueSearch t) → h t }
ps (Γ , A₁ ∨ A₂ ⟶ B ∣ Δ ⊢ C ∙ S) (acc rs)
 with ps (Γ ∣ A₁ ∨ A₂ ⟶ B ,, Δ ⊢ C ∙ S) (rs (f⟨-wf Γ Δ (A₁ ∨ A₂ ⟶ B) C S))
... | left  h = left (continueSearch h)
... | right h = right λ{ (continueSearch t) → h t }
ps (Γ , (A₁ ⟶ A₂) ⟶ B ∣ Δ ⊢ C ∙ S) (acc rs)
 with ps (Γ ∣ (A₁ ⟶ A₂) ⟶ B ,, Δ ⊢ C ∙ S) (rs (f⟨-wf Γ Δ ((A₁ ⟶ A₂) ⟶ B) C S))
... | left  h = left (continueSearch h)
... | right h = right λ{ (continueSearch t) → h t }

-- The final, guaranteed to terminate proof searching procedure.
isProvable : (s : SequentWithCursorAndMode)
            → Either (derivationFor s) (¬ derivationFor s)
isProvable s = ps s (≺-wf s)
