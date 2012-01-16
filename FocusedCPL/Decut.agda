-- Constructive Provability Logic
-- Focused variant
-- Robert J. Simmons, Bernardo Toninho

-- Removing an assumption given evidence

open import Prelude hiding (⊥; [_])
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import FocusedCPL.Core
open import FocusedCPL.Evidence

module FocusedCPL.Decut where

module DECUT (UWF : UpwardsWellFounded) where
  open TRANS-UWF UWF
  open ILIST UWF
  open SEQUENT UWF
  open EVIDENCE UWF

  decutV : ∀{wc w Γ A B} (Γ' : MCtx)
    → Term [] (Γ' ++ Γ) w · (Reg A)
    → Value [] (Γ' ++ Γ) wc B
    → Value [] (Γ' ++ (↓ A at w) :: Γ) wc B

  decutN : ∀{wc w Γ A B Ω} (Γ' : MCtx)
    → Term [] (Γ' ++ Γ) w · (Reg A)
    → Term [] (Γ' ++ Γ) wc Ω B
    → Term [] (Γ' ++ (↓ A at w) :: Γ) wc Ω B

  decutV Γ' N (pR x) = pR {! -- regular old weakening --!}
  decutV Γ' N (↓R N₁) = ↓R {!!}
  decutV Γ' N (◇R ω N₁) = {!!}
  decutV Γ' N (□R N₁) = {!!}

  decutN Γ' N (L pf⁺ N₁) = L pf⁺ (decutN (_ :: Γ') {!N!} N₁)
  decutN Γ' N (↓L pf⁻ ωh x Sp) = {!!}
  decutN Γ' N ⊥L = {!!}
  decutN Γ' N (◇L N₁) = {!!}
  decutN Γ' N (□L N₁) = {!!}
  decutN Γ' N (↑R V₁) = {!!}
  decutN Γ' N (⊃R N₁) = {!!}