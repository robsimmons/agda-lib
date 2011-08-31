-- Normal forms for natural deduction in Full Infon Logic
-- Robert J. Simmons

open import Prelude hiding (⊤)
open import Infon.Core

module Infon.NormalForms where

module NORMAL-FORMS (Prin : Set; _≡?_ : (p q : Prin) → Decidable (p ≡ q)) where

   open CORE Prin _≡?_

   ---------------------------------
   -- Judgmental Full Infon Logic --
   ---------------------------------

   infix 1 _⊢_verif
   infix 1 _⊢_use
   mutual
      data _⊢_verif (Γ : Ctx) : Type → Set where
         ↓↑ : ∀{Q} 
            → (D : Γ ⊢ (atom Q) use)
            → Γ ⊢ (atom Q) verif
         ⊤I : Γ ⊢ ⊤ verif
         ⊃I : ∀{A B}
            → (D : (A true) :: Γ ⊢ B verif)
            → Γ ⊢ A ⊃ B verif
         ∧I : ∀{A B}
            → (D : Γ ⊢ A verif)
            → (E : Γ ⊢ B verif)
            → Γ ⊢ A ∧ B verif
         □I : ∀{A p} 
            → (D : Γ ○ p ⊢ A verif)
            → Γ ⊢ □ p A verif
         □E : ∀{A p C}
            → (D : Γ ⊢ □ p A use)
            → (E : (p said A) :: Γ ⊢ C verif)
            → Γ ⊢ C verif
         ■I : ∀{A p} 
            → (D : Γ ● p ⊢ A verif)
            → Γ ⊢ ■ p A verif
         ■E : ∀{A p C}
            → (D : Γ ⊢ ■ p A use)
            → (E : (p implied A) :: Γ ⊢ C verif)
            → Γ ⊢ C verif

      data _⊢_use (Γ : Ctx) : Type → Set where
         hyp : ∀{A} 
            → (x : (A true) ∈ Γ) 
            → Γ ⊢ A use
         ⊃E : ∀{A B} 
            → (D : Γ ⊢ A ⊃ B use)
            → (E : Γ ⊢ A verif) 
            → Γ ⊢ B use
         ∧E₁ : ∀{A B}
            → (D : Γ ⊢ A ∧ B use)
            → Γ ⊢ A use
         ∧E₂ : ∀{A B}
            → (D : Γ ⊢ A ∧ B use)
            → Γ ⊢ B use

   mutual 
      wkN : ∀{Γ Γ' A} → Γ ⊆ Γ' → Γ ⊢ A verif → Γ' ⊢ A verif
      wkN θ (↓↑ D) = ↓↑ (wkR θ D)
      wkN θ ⊤I = ⊤I
      wkN θ (⊃I D) = ⊃I (wkN (sub-cons-congr θ) D)
      wkN θ (∧I D E) = ∧I (wkN θ D) (wkN θ E)
      wkN θ (□I D) = □I (wkN (congr○ θ) D)
      wkN θ (□E D E) = □E (wkR θ D) (wkN (sub-cons-congr θ) E)
      wkN θ (■I D) = ■I (wkN (congr● θ) D)
      wkN θ (■E D E) = ■E (wkR θ D) (wkN (sub-cons-congr θ) E)

      wkR : ∀{Γ Γ' A} → Γ ⊆ Γ' → Γ ⊢ A use → Γ' ⊢ A use
      wkR θ (hyp x) = hyp (θ x)
      wkR θ (⊃E D E) = ⊃E (wkR θ D) (wkN θ E)
      wkR θ (∧E₁ D) = ∧E₁ (wkR θ D)
      wkR θ (∧E₂ D) = ∧E₂ (wkR θ D)

   mutual
      substRN : ∀{Γ A C} (Γ' : Ctx) 
         → Γ ⊢ A use
         → Γ' ++ (A true) :: Γ ⊢ C verif
         → Γ' ++ Γ ⊢ C verif
      substRN Γ' D (↓↑ E) = ↓↑ (substRR Γ' D E)
      substRN Γ' D ⊤I = ⊤I
      substRN Γ' D (⊃I E) = ⊃I (substRN (_ :: Γ') D E)
      substRN Γ' D (∧I E₁ E₂) = 
         ∧I (substRN Γ' D E₁) (substRN Γ' D E₂)
      substRN Γ' D (□I E) = □I (wkN (sub-eq (eq○true Γ')) E)
      substRN Γ' D (□E E₁ E₂) =
         □E (substRR Γ' D E₁) (substRN (_ :: Γ') D E₂)
      substRN Γ' D (■I E) = ■I (wkN (sub-eq (eq●true Γ')) E)
      substRN Γ' D (■E E₁ E₂) = 
         ■E (substRR Γ' D E₁) (substRN (_ :: Γ') D E₂)

      substRR : ∀{Γ A C} (Γ' : Ctx)
         → Γ ⊢ A use
         → Γ' ++ (A true) :: Γ ⊢ C use
         → Γ' ++ Γ ⊢ C use
      substRR [] D (hyp Z) = D
      substRR [] D (hyp (S n)) = hyp n
      substRR (._ :: Γ') D (hyp Z) = hyp Z
      substRR (_ :: Γ') D (hyp (S x)) = wkR sub-cons (substRR Γ' D (hyp x))
      substRR Γ' D (⊃E E₁ E₂) = ⊃E (substRR Γ' D E₁) (substRN Γ' D E₂)
      substRR Γ' D (∧E₁ E) = ∧E₁ (substRR Γ' D E)
      substRR Γ' D (∧E₂ E) = ∧E₂ (substRR Γ' D E)