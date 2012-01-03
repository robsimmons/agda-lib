-- Sequent Calculus for Full Infon Logic
-- Robert J. Simmons

open import Prelude
open import Infon.Core
open import Infon.SequentCore
open import Infon.SequentCut

module Infon.Sequent where

module SEQUENT {Prin} (_≡?_ : (p q : Prin) → Decidable (p ≡ q)) where

   open CORE _≡?_
   open SEQUENT-CORE _≡?_ public
   open SEQUENT-CUT _≡?_ public

   cut' : ∀{Γ A C} → Γ ⇒ A → (A true) :: Γ ⇒ C → Γ ⇒ C
   cut' D E = cut (→m D) (→m E)

   cut□' : ∀{Γ A C p} → Γ ○ p ⇒ A → (p said A) :: Γ ⇒ C → Γ ⇒ C
   cut□' D E = cut□ D (→m E)

   cut■' : ∀{Γ A C p} → Γ ● p ⇒ A → (p implied A) :: Γ ⇒ C → Γ ⇒ C
   cut■' D E = cut■ D (→m E)

