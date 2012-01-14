-- Constructive Provability Logic
-- Focused variant
-- Robert J. Simmons, Bernardo Toninho

-- Master induction hypothesis for cut elimination

open import Prelude hiding (⊥; [_])
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import FocusedCPL.Core

module FocusedCPL.IH where

module IH (UWF : UpwardsWellFounded) where
  open TRANS-UWF UWF
  open ILIST UWF
  open SEQUENT UWF

  record P (wc : W) : Set where
   field 
    subst⁺ : ∀{Γ A C}
      → Value [] Γ wc A
      → Term [] Γ wc (I A wc) (Reg C)
      → Term [] Γ wc · (Reg C)

    rsubstV : ∀{Γ w A C} 
      (Γ' : MCtx)
      → Term [] (Γ' ++ Γ) w · (Reg A)
      → Value [] (Γ' ++ ↓ A at w :: Γ) wc C
      → Value [] (Γ' ++ Γ) wc C

    rsubstN : ∀{Γ w A C} 
      (Γ' : MCtx)
      → Term [] (Γ' ++ Γ) w · (Reg A)
      → Term [] (Γ' ++ ↓ A at w :: Γ) wc · (Reg C)
      → Term [] (Γ' ++ Γ) wc · (Reg C)
