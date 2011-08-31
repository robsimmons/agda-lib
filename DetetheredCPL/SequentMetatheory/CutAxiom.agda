-- Constructive Provability Logic 
-- De-tethered intuitionistic variant
-- Robert J. Simmons, Bernardo Toninho

-- Since Cut.agda takes forever to load with or without the 
-- termination check, we just postulate the cut principle to give ourselves
-- the option of leaving the actual proof out of the larger development

module DetetheredCPL.SequentMetatheory.CutAxiom where
open import Prelude hiding (⊥)
open import Accessibility.Inductive 
open import Accessibility.IndexedList
open import DetetheredCPL.Core 
open import DetetheredCPL.SequentMetatheory.Core
open import DetetheredCPL.SequentMetatheory.IH

module SEQUENT-CUT (UWF : UpwardsWellFounded 
   ; dec≺ : (w w' : _) → Decidable (TRANS-UWF._≺*_ UWF w w')) where
   open TRANS-UWF UWF
   open ILIST UWF
   open CORE UWF 
   open SEQUENT-IH UWF dec≺

   postulate 
      cutP : (wc : W) → ((wc' : W) → wc ≺+ wc' → P wc') → ∀{Γ w A C}
            → Γ ⇒ A [ w ]
            → A at w :: Γ ⇒ C [ wc ]
            → Γ ⇒ C [ wc ]