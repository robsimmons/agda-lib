-- Soundness of Primal Infon Logic relative to Full Infon Logic
-- Done in sequent-calculus-land because, why not?

open import Prelude
open import Infon.Core
import Infon.Sequent
import Primal.Sequent

module Primal.Sound where

module SOUND {Prin : Set} (_≡?_ : (p q : Prin) → Decidable (p ≡ q)) where

   open CORE _≡?_
   open Infon.Sequent.SEQUENT _≡?_ 
      hiding (cut ; cut' ; cut□ ; cut□' ; cut■ ; cut■')
   open Primal.Sequent.SEQUENT _≡?_ 
      hiding (cut ; cut' ; cut□ ; cut□' ; cut■ ; cut■' ; Seq)
      renaming (wk to wkp ; wk' to wkp' ; _⇒_ to _⇒'_ ; m→ to m→' ; →m to →m')

   sound : ∀{Γ A} → Γ ⇒' A → Γ ⇒ A
   sound (init x) = ident x
   sound (⊃R D) = ⊃R (wk' sub-wken (sound D))
   sound (⊃L x D E) = ⊃L x (sound D) (sound E)
   sound (∧R D E) = ∧R (sound D) (sound E)
   sound (∧L₁ x D) = ∧L₁ x (sound D)
   sound (∧L₂ x D) = ∧L₂ x (sound D)
   sound (□R D) = □R (sound D)
   sound (□L x D) = □L x (sound D)
   sound (■R D) = ■R (sound D)
   sound (■L x D) = ■L x (sound D)