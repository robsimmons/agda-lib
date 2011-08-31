-- Constructive Provability Logic 
-- De-tethered intuitionstic variant
-- Robert J. Simmons, Bernardo Toninho

-- Soundness and completeness of the sequent calculus

module DetetheredCPL.Sequent where
open import Prelude hiding (⊥)
open import Accessibility.Inductive 
open import Accessibility.IndexedList
open import DetetheredCPL.Core 
open import DetetheredCPL.SequentMetatheory.Core
open import DetetheredCPL.SequentMetatheory.IH
open import DetetheredCPL.SequentMetatheory.PostCut

module SEQUENT (UWF : UpwardsWellFounded
   ; dec≺ : (w w' : _) → Decidable (TRANS-UWF._≺*_ UWF w w')) where
   open TRANS-UWF UWF
   open ILIST UWF
   open CORE UWF 
   open SEQUENT-CORE UWF dec≺ public
   open SEQUENT-IH UWF dec≺
   open SEQUENT-POST-CUT UWF dec≺

   ident : ∀{Γ A wc} → A at wc ∈ Γ → Γ ⇒ A [ wc ]
   ident = P.ident cut-thms

   cut : ∀{Γ w wc A C} → Γ ⇒ A [ w ] → A at w :: Γ ⇒ C [ wc ] → Γ ⇒ C [ wc ]
   cut = P.cut cut-thms

   decut : ∀{Γ w wc A C} → Γ ⇒ A [ w ] → Γ ⇒ C [ wc ] → A at w :: Γ ⇒ C [ wc ]
   decut = P.decut cut-thms

   wkS : ∀{Γ Γ' w A} → Γ ⊆ Γ' to w → Γ ⇒ A [ w ] → Γ' ⇒ A [ w ]
   wkS = wk

   ⊃E' : ∀{Γ w A B} → Γ ⇒ A ⊃ B [ w ] → Γ ⇒ A [ w ] → Γ ⇒ B [ w ]
   ⊃E' = P.⊃E' cut-thms

   