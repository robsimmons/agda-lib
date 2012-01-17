-- Constructive Provability Logic
-- Focused variant
-- Robert J. Simmons, Bernardo Toninho

-- Admissibility of cut (and decut)

open import Prelude hiding (⊥)
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import FocusedCPL.Core 
open import FocusedCPL.Weakening
import FocusedCPL.Cut.Evidence
import FocusedCPL.Cut.IH
import FocusedCPL.Cut.Pre
import FocusedCPL.Cut.Main

module FocusedCPL.Cut where

module CUT 
  (UWF : UpwardsWellFounded)
  (dec≺ : (w w' : _) → Decidable (TRANS-UWF._≺*_ UWF w w')) where
  open TRANS-UWF UWF
  open FocusedCPL.Cut.Evidence UWF
  open FocusedCPL.Cut.IH UWF
  open FocusedCPL.Cut.Pre UWF
  open FocusedCPL.Cut.Main UWF
  open ILIST UWF
  open SEQUENT UWF
  open WEAKENING UWF
  open EVIDENCE dec≺
  open IH dec≺

  PF : ∀{wc} → P wc
  PF {wc} = ind+ P (λ wc ih → 
   record {
    subst⁺ = MAIN-STEP.subst⁺ dec≺ wc ih;
    subst⁻ = MAIN-STEP.subst⁻ dec≺ wc ih;
    --
    rsubstV = MAIN-STEP.rsubstV dec≺ wc ih;
    rsubstN = MAIN-STEP.rsubstN dec≺ wc ih;
    rsubstSp = MAIN-STEP.rsubstSp dec≺ wc ih;
    --
    lsubstN = MAIN-STEP.lsubstN dec≺ wc ih;
    lsubstSp = MAIN-STEP.lsubstSp dec≺ wc ih;
    --
    decutV = PRE-STEP.decutV dec≺ wc ih;
    decutN = PRE-STEP.decutN dec≺ wc ih;
    decutSp = PRE-STEP.decutSp dec≺ wc ih}) wc

  subst⁺ : ∀{wc} → Psubst⁺ wc
  subst⁺ = P.subst⁺ PF

  subst⁻ : ∀{wc} → Psubst⁻ wc
  subst⁻ = P.subst⁻ PF

  rsubstV : ∀{wc} → PrsubstV wc
  rsubstV = P.rsubstV PF

  rsubstN : ∀{wc} → PrsubstN wc
  rsubstN = P.rsubstN PF

  rsubstSp : ∀{wc} → PrsubstSp wc
  rsubstSp = P.rsubstSp PF

  lsubstN : ∀{wc} → PlsubstN wc
  lsubstN = P.lsubstN PF

  lsubstSp : ∀{wc} → PlsubstSp wc
  lsubstSp = P.lsubstSp PF

  decutV : ∀{wc} → PdecutV wc
  decutV = P.decutV PF

  decutN : ∀{wc} → PdecutN wc
  decutN = P.decutN PF

  decutSp : ∀{wc} → PdecutSp wc
  decutSp = P.decutSp PF
  