-- Sequent Calculus for Primal Infon Logic
-- Shortcut: postulate cut instead of spending a week compiling it
-- Robert J. Simmons

open import Prelude
open import Infon.Core
open import Primal.SequentCore

module Primal.SequentAxiom where

module SEQUENT-CUT (Prin : Set; _≡?_ : (p q : Prin) → Decidable (p ≡ q)) where

   open CORE Prin _≡?_
   open SEQUENT-CORE Prin _≡?_

   postulate cut : ∀{Γ d e A C} 
                → Seq Γ d A
                → Seq ((A true) :: Γ) e C 
                → Γ ⇒ C

   postulate cut□ : ∀{p Γ e A C} 
                → Γ ○ p ⇒ A
                → Seq ((p said A) :: Γ) e C 
                → Γ ⇒ C

   postulate cut■ : ∀{p Γ e A C} 
                → Γ ● p ⇒ A
                → Seq ((p implied A) :: Γ) e C 
                → Γ ⇒ C

