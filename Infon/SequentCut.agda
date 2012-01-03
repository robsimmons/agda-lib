-- Cut admissibility for Full Infon Logic
-- Just the cut principle, which is difficult for Agda to compile
-- Robert J. Simmons

open import Prelude
open import Infon.Core
open import Infon.SequentCore

module Infon.SequentCut where

module SEQUENT-CUT {Prin} (_≡?_ : (p q : Prin) → Decidable (p ≡ q)) where

   open CORE _≡?_
   open SEQUENT-CORE _≡?_

   -----------------------
   -- Cut admissibility --
   -----------------------

   mutual

      -----------
      -- Truth --
      -----------

      cut : ∀{Γ d e A C} 
         → Seq Γ d A
         → Seq ((A true) :: Γ) e C 
         → Γ ⇒ C

      -- Principal cuts
      cut (init x) (init Z) = init x
      cut (⊃R D) (⊃L Z E₁ E₂) = 
         cut (→m (cut (→m (cut (⊃R D) E₁)) D))
          (→m (cut (wk sub-wken (⊃R D)) (wk sub-exch E₂)))
      cut (∧R D₁ D₂) (∧L₁ Z E) = 
         cut D₁ (→m (cut (wk sub-wken (∧R D₁ D₂)) (wk sub-exch E)))
      cut (∧R D₁ D₂) (∧L₂ Z E) = 
         cut D₂ (→m (cut (wk sub-wken (∧R D₁ D₂)) (wk sub-exch E)))
      cut (□R D) (□L Z E) = 
         cut□ (m→ D) (→m (cut (wk sub-wken (□R D)) (wk sub-exch E)))
      cut (■R D) (■L Z E) = 
         cut■ (m→ D) (→m (cut (wk sub-wken (■R D)) (wk sub-exch E)))

      -- Left commutative cuts
      cut (⊃L x D₁ D₂) E = ⊃L x (m→ D₁) (cut D₂ (wk sub-wkex E))
      cut (∧L₁ x D) E = ∧L₁ x (cut D (wk sub-wkex E))
      cut (∧L₂ x D) E = ∧L₂ x (cut D (wk sub-wkex E))
      cut (□L x D) E = □L x (cut D (wk sub-wkex E))
      cut (■L x D) E = ■L x (cut D (wk sub-wkex E))

      -- Right commutative cuts
      cut D (init (S x)) = init x
      cut D ⊤R = ⊤R
      cut D (⊃R E) = ⊃R (cut (wk sub-wken D) (wk sub-exch E))
      cut D (⊃L (S x) E₁ E₂) = 
         ⊃L x (cut D E₁) (cut (wk sub-wken D) (wk sub-exch E₂))
      cut D (∧R E₁ E₂) = ∧R (cut D E₁) (cut D E₂)
      cut D (∧L₁ (S x) E) = ∧L₁ x (cut (wk sub-wken D) (wk sub-exch E))
      cut D (∧L₂ (S x) E) = ∧L₂ x (cut (wk sub-wken D) (wk sub-exch E))
      cut D (□R E) = □R (m→ E)
      cut D (□L (S x) E) = □L x (cut (wk sub-wken D) (wk sub-exch E))
      cut D (■R E) = ■R (m→ E)
      cut D (■L (S x) E) = ■L x (cut (wk sub-wken D) (wk sub-exch E))

      ----------
      -- Said --
      ----------

      cut□ : ∀{p Γ e A C} 
         → Γ ○ p ⇒ A
         → Seq ((p said A) :: Γ) e C 
         → Γ ⇒ C
      cut□ D (init (S x)) = init x
      cut□ D ⊤R = ⊤R
      cut□ D (⊃R E) = ⊃R (cut□ D (wk sub-exch E))
      cut□ D (⊃L (S x) E₁ E₂) = ⊃L x (cut□ D E₁) (cut□ D (wk sub-exch E₂))
      cut□ D (∧R E₁ E₂) = ∧R (cut□ D E₁) (cut□ D E₂)
      cut□ D (∧L₁ (S x) E) = ∧L₁ x (cut□ D (wk sub-exch E))
      cut□ D (∧L₂ (S x) E) = ∧L₂ x (cut□ D (wk sub-exch E))
      cut□ {p} D (□R {q} E) with q ≡? p 
      cut□ D (□R E) | Inl Refl = □R (cut (→m D) E)
      cut□ D (□R E) | Inr _ = □R (m→ E)
      cut□ {p} {Γ} D (□L {q} (S x) E) = 
         □L x (cut□ (wk' (congr○ {Γ} {p} {(q said _) :: Γ} sub-wken) D)
                (wk sub-exch E))
      cut□ {p} D (■R {q} E) with q ≡? p
      cut□ {p} {Γ} D (■R E) | Inl Refl = ■R (cut (wk (sub-○● Γ) (→m D)) E)
      cut□ D (■R E) | Inr _ = ■R (m→ E)
      cut□ D (■L (S x) E) = ■L x (cut□ D (wk sub-exch E))

      -------------
      -- Implied --
      -------------

      cut■ : ∀{p Γ e A C} 
         → Γ ● p ⇒ A
         → Seq ((p implied A) :: Γ) e C 
         → Γ ⇒ C
      cut■ D (init (S x)) = init x
      cut■ D ⊤R = ⊤R
      cut■ D (⊃R E) = ⊃R (cut■ D (wk sub-exch E))
      cut■ D (⊃L (S x) E₁ E₂) = ⊃L x (cut■ D E₁) (cut■ D (wk sub-exch E₂))
      cut■ D (∧R E₁ E₂) = ∧R (cut■ D E₁) (cut■ D E₂)
      cut■ D (∧L₁ (S x) E) = ∧L₁ x (cut■ D (wk sub-exch E))
      cut■ D (∧L₂ (S x) E) = ∧L₂ x (cut■ D (wk sub-exch E))
      cut■ {p} D (□R {q} E) = □R (m→ E)
      cut■ {p} {Γ} D (□L {q} (S x) E) = 
         □L x (cut■ (wk' (congr● {Γ} {p} {(q said _) :: Γ} sub-wken) D) 
          (wk sub-exch E))
      cut■ {p} D (■R {q} E) with q ≡? p
      cut■ D (■R E) | Inl Refl = ■R (cut (→m D) E)
      cut■ D (■R E) | Inr _ = ■R (m→ E)
      cut■ {p} {Γ} D (■L {q} (S x) E) = 
         ■L x (cut■ (wk' (congr● {Γ} {p} {(q implied _) :: Γ} sub-wken) D) 
          (wk sub-exch E))

