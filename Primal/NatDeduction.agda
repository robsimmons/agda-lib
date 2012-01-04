-- Natural Deduction for Primal Infon Logic
-- Robert J. Simmons

open import Prelude hiding (⊤)
open import Infon.Core

module Primal.NatDeduction where

module NAT-DEDUCTION {Prin} (_≡?_ : (p q : Prin) → Decidable (p ≡ q)) where

   open CORE _≡?_

   ---------------------------------
   -- Judgmental Full Infon Logic --
   ---------------------------------

   infix 1 _⊢_
   data _⊢_ (Γ : Ctx) : Type → Set where
      hyp : ∀{A} 
         → (x : (A true) ∈ Γ) 
         → Γ ⊢ A
      ⊤I : Γ ⊢ ⊤
      ⊃I : ∀{A B}
         → (D : Γ ⊢ B)
         → Γ ⊢ A ⊃ B
      ⊃E : ∀{A B} 
         → (D : Γ ⊢ A ⊃ B)
         → (E : Γ ⊢ A) 
         → Γ ⊢ B
      ∧I : ∀{A B}
         → (D : Γ ⊢ A)
         → (E : Γ ⊢ B)
         → Γ ⊢ A ∧ B
      ∧E₁ : ∀{A B}
         → (D : Γ ⊢ A ∧ B)
         → Γ ⊢ A
      ∧E₂ : ∀{A B}
         → (D : Γ ⊢ A ∧ B)
         → Γ ⊢ B
      □I : ∀{A p} 
         → (D : Γ ○ p ⊢ A)
         → Γ ⊢ □ p A
      □E : ∀{A p C}
         → (D : Γ ⊢ □ p A)
         → (E : (p said A) :: Γ ⊢ C)
         → Γ ⊢ C 
      ■I : ∀{A p} 
         → (D : Γ ● p ⊢ A)
         → Γ ⊢ ■ p A
      ■E : ∀{A p C}
         → (D : Γ ⊢ ■ p A)
         → (E : (p implied A) :: Γ ⊢ C)
         → Γ ⊢ C 



   -------------------------
   -- Weakening principle --
   -------------------------

   wk : ∀{Γ Γ' A} → Γ ⊆ Γ' → Γ ⊢ A → Γ' ⊢ A
   wk θ (hyp x) = hyp (θ x)
   wk θ ⊤I = ⊤I
   wk θ (⊃I D) = ⊃I (wk θ D)
   wk θ (⊃E D E) = ⊃E (wk θ D) (wk θ E)
   wk θ (∧I D E) = ∧I (wk θ D) (wk θ E)
   wk θ (∧E₁ D) = ∧E₁ (wk θ D)
   wk θ (∧E₂ D) = ∧E₂ (wk θ D)
   wk θ (□I D) = □I (wk (congr○ θ) D)
   wk θ (□E D E) = □E (wk θ D) (wk (sub-cons-congr θ) E)
   wk θ (■I D) = ■I (wk (congr● θ) D)
   wk θ (■E D E) = ■E (wk θ D) (wk (sub-cons-congr θ) E)



   ---------------------------------
   -- Normal (truth) substitution --
   ---------------------------------

   subst : ∀{A C Γ} (Γ' : Ctx)
      → Γ ⊢ A 
      → Γ' ++ (A true) :: Γ ⊢ C
      → Γ' ++ Γ ⊢ C 

   -- Variable cases
   subst [] D (hyp Z) = D
   subst [] D (hyp (S x)) = hyp x
   subst Γ' D ⊤I = ⊤I
   subst (._ :: Γ') D (hyp Z) = hyp Z
   subst (_ :: Γ') D (hyp (S n)) = wk sub-cons (subst Γ' D (hyp n))

   -- Structural cases
   subst Γ' D (⊃I E) = ⊃I (subst Γ' D E)
   subst Γ' D (⊃E E₁ E₂) = ⊃E (subst Γ' D E₁) (subst Γ' D E₂)
   subst Γ' D (∧I E₁ E₂) = ∧I (subst Γ' D E₁) (subst Γ' D E₂)
   subst Γ' D (∧E₁ E) = ∧E₁ (subst Γ' D E)
   subst Γ' D (∧E₂ E) = ∧E₂ (subst Γ' D E)
   subst {A} {□ p C} {Γ} Γ' D (□I E) = □I (wk (sub-eq (eq○true Γ')) E)
   subst Γ' D (□E E₁ E₂) = □E (subst Γ' D E₁) (subst (_ :: Γ') D E₂)
   subst {A} {■ p C} {Γ} Γ' D (■I E) = ■I (wk (sub-eq (eq●true Γ')) E)
   subst Γ' D (■E E₁ E₂) = ■E (subst Γ' D E₁) (subst (_ :: Γ') D E₂)



   -------------------------
   -- "Said" substitution --
   -------------------------

   subst□ : ∀{p A C Γ} (Γ' : Ctx)
      → Γ ○ p ⊢ A
      → Γ' ++ (p said A) :: Γ ⊢ C
      → Γ' ++ Γ ⊢ C

   -- Variable case (nothing interesting happens here)
   subst□ {p} {A} {C} {Γ} Γ' D (hyp x) = hyp (lem Γ' x)
    where 
      lem : (Γ' : _)→ (C true) ∈ (Γ' ++ (p said A) :: Γ) → (C true) ∈ Γ' ++ Γ
      lem [] (S x) = x
      lem (._ :: Γ) Z = Z
      lem (_ :: Γ) (S x) = S (lem Γ x)

   -- Structural cases
   subst□ Γ' D ⊤I = ⊤I
   subst□ Γ' D (⊃I E) = ⊃I (subst□ Γ' D E)
   subst□ Γ' D (⊃E E₁ E₂) = ⊃E (subst□ Γ' D E₁) (subst□ Γ' D E₂)
   subst□ Γ' D (∧I E₁ E₂) = ∧I (subst□ Γ' D E₁) (subst□ Γ' D E₂)
   subst□ Γ' D (∧E₁ E) = ∧E₁ (subst□ Γ' D E)
   subst□ Γ' D (∧E₂ E) = ∧E₂ (subst□ Γ' D E)
   subst□ {p} {A} {□ q C} {Γ} Γ' D (□I E) = □I E₂ 
    where
      -- Rewrite erasure-of-union as union-of-erasure
      E₁ : Γ' ○ q ++ ((p said A) :: Γ) ○ q ⊢ C
      E₁ = wk (sub-eq (hmorph○ Γ')) E

      -- Substitute or throw away, depending on equality of p and q
      call-subst : ∀{q} 
         → Γ' ○ q ++ ((p said A) :: Γ) ○ q ⊢ C
         → Γ' ○ q ++ Γ ○ q ⊢ C
      call-subst {q} E with q ≡? p
      call-subst E | Inl Refl = subst (Γ' ○ p) D E
      call-subst E | Inr _ = E

      -- Rewrite union-of-erasure as erasure-of-union
      E₂ : (Γ' ++ Γ) ○ q ⊢ C
      E₂ = wk (sub-eq (ID.symm (hmorph○ Γ'))) (call-subst E₁)
   subst□ Γ' D (□E E₁ E₂) = □E (subst□ Γ' D E₁) (subst□ (_ :: Γ') D E₂)
   subst□ {p} {A} {■ q C} {Γ} Γ' D (■I E) = ■I E₂
    where
      -- Rewrite erasure-of-union as union-of-erasure
      E₁ : Γ' ● q ++ ((p said A) :: Γ) ● q ⊢ C
      E₁ = wk (sub-eq (hmorph● Γ')) E

      -- Substitute or throw away, depending on equality of p and q
      call-subst : ∀{q} 
         → Γ' ● q ++ ((p said A) :: Γ) ● q ⊢ C
         → Γ' ● q ++ Γ ● q ⊢ C
      call-subst {q} E with q ≡? p
      call-subst E | Inl Refl = subst (Γ' ● p) (wk (sub-○● Γ) D) E
      call-subst E | Inr _ = E

      -- Rewrite union-of-erasure as erasure-of-union
      E₂ : (Γ' ++ Γ) ● q ⊢ C
      E₂ = wk (sub-eq (ID.symm (hmorph● Γ'))) (call-subst E₁)
   subst□ Γ' D (■E E₁ E₂) = ■E (subst□ Γ' D E₁) (subst□ (_ :: Γ') D E₂)



   ----------------------------   
   -- "Implied" substitution --
   ----------------------------

   subst■ : ∀{p A C Γ} (Γ' : Ctx)
      → Γ ● p ⊢ A
      → Γ' ++ (p implied A) :: Γ ⊢ C
      → Γ' ++ Γ ⊢ C

   -- Variable case (nothing interesting happens here)
   subst■ {p} {A} {C} {Γ} Γ' D (hyp x) = hyp (lem Γ' x)
    where 
      lem : (Γ' : _)→ (C true) ∈ (Γ' ++ (p implied A) :: Γ) → (C true) ∈ Γ' ++ Γ
      lem [] (S x) = x
      lem (._ :: Γ) Z = Z
      lem (_ :: Γ) (S x) = S (lem Γ x)

   -- Structural cases
   subst■ Γ' D ⊤I = ⊤I
   subst■ Γ' D (⊃I E) = ⊃I (subst■ Γ' D E)
   subst■ Γ' D (⊃E E₁ E₂) = ⊃E (subst■ Γ' D E₁) (subst■ Γ' D E₂)
   subst■ Γ' D (∧I E₁ E₂) = ∧I (subst■ Γ' D E₁) (subst■ Γ' D E₂)
   subst■ Γ' D (∧E₁ E) = ∧E₁ (subst■ Γ' D E)
   subst■ Γ' D (∧E₂ E) = ∧E₂ (subst■ Γ' D E)
   subst■ {p} {A} {□ q C} {Γ} Γ' D (□I E) = □I (wk (sub-eq (eq○implied Γ')) E)
   subst■ Γ' D (□E E₁ E₂) = □E (subst■ Γ' D E₁) (subst■ (_ :: Γ') D E₂)
   subst■ {p} {A} {■ q C} {Γ} Γ' D (■I E) = ■I E₂
    where
      -- Rewrite erasure-of-union as union-of-erasure
      E₁ : Γ' ● q ++ ((p implied A) :: Γ) ● q ⊢ C
      E₁ = wk (sub-eq (hmorph● Γ')) E

      -- Substitute or throw away, depending on equality of p and q
      call-subst : ∀{q} 
         → Γ' ● q ++ ((p implied A) :: Γ) ● q ⊢ C
         → Γ' ● q ++ Γ ● q ⊢ C
      call-subst {q} E with q ≡? p
      call-subst E | Inl Refl = subst (Γ' ● p) D E
      call-subst E | Inr _ = E

      -- Rewrite union-of-erasure as erasure-of-union
      E₂ : (Γ' ++ Γ) ● q ⊢ C
      E₂ = wk (sub-eq (ID.symm (hmorph● Γ'))) (call-subst E₁)
   subst■ Γ' D (■E E₁ E₂) = ■E (subst■ Γ' D E₁) (subst■ (_ :: Γ') D E₂)
