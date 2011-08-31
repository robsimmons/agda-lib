-- Constructive Provability Logic 
-- De-tethered intuitionistic variant
-- Robert J. Simmons, Bernardo Toninho

module DetetheredCPL.SequentMetatheory.IH where
open import Prelude hiding (⊥)
open import Accessibility.Inductive 
open import Accessibility.IndexedList
open import DetetheredCPL.Core 
open import DetetheredCPL.SequentMetatheory.Core

module SEQUENT-IH
  (UWF : UpwardsWellFounded 
   ; dec≺ : (w w' : _) → Decidable (TRANS-UWF._≺*_ UWF w w')) where
   open TRANS-UWF UWF
   open ILIST UWF
   open CORE UWF 
   open SEQUENT-CORE UWF dec≺

   record P (wc : W) : Set where
      field
         ident : ∀{Γ A}
            → A at wc ∈ Γ
            → Γ ⇒ A [ wc ]
         cut : ∀{Γ w A C}
            → Γ ⇒ A [ w ]
            → A at w :: Γ ⇒ C [ wc ]
            → Γ ⇒ C [ wc ]
         decut : ∀{Γ w A C}
            → Γ ⇒ A [ w ] 
            → Γ ⇒ C [ wc ]
            → A at w :: Γ ⇒ C [ wc ]
         decutM : ∀{Γ Δ w A C s}
            → Δ ⊆ Γ pr wc
            → Γ ⇒ A [ w ] 
            → Δ / Γ ⇒ C [ wc ]/ s
            → Δ / A at w :: Γ ⇒ C [ wc ]/ s
         extend : ∀{Δ Γ A w} 
            → Δ ⊆ Γ pr wc
            → Δ ⇒ A [ w ] 
            → Δ ⊆ A at w :: Γ pr wc 
         subst : ∀{A Δ Γ} 
            → Δ ⊆ Γ pr wc 
            → Δ ⇒ A [ wc ] 
            → Γ ⇒ A [ wc ]
         →m : ∀{Γ Δ A} 
            → Δ ⊆ Γ pr wc 
            → Γ ⇒ A [ wc ] 
            → ∃ λ s → Δ / Γ ⇒ A [ wc ]/ s
         m→ : ∀{Γ Δ A s} 
            → Δ ⊆ Γ pr wc 
            → Δ / Γ ⇒ A [ wc ]/ s
            → Γ ⇒ A [ wc ] 
         ⊃E' : ∀{Δ A B} 
            → Δ ⇒ A ⊃ B [ wc ]
            → Δ ⇒ A [ wc ] 
            → Δ ⇒ B [ wc ]
         ⊥E' : ∀{Δ A w} 
            → wc ≺* w
            → Δ ⇒ ⊥ [ w ]
            → Δ ⇒ A [ wc ] 
         ◇E' : ∀{Δ A C w} 
            → wc ≺* w
            → Δ ⇒ ◇ A [ w ]
            → (∀{w'} → w ≺ w' → Δ ⇒ A [ w' ] → Δ ⇒ C [ wc ])
            → Δ ⇒ C [ wc ] 
