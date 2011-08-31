-- A syntactic account of Primal Infon Logic

open import Prelude
open import Infon.Core
import Infon.NormalForms
import Primal.NormalForms

module Primal.Restriction2 where

module RESTRICTION (Prin : Set; _≡?_ : (p q : Prin) → Decidable (p ≡ q)) where

   open CORE Prin _≡?_
   open Infon.NormalForms.NORMAL-FORMS Prin _≡?_ 
   open Primal.NormalForms.NORMAL-FORMS Prin _≡?_ 
      renaming (_⊢_verif to _⊢_verif' ; _⊢_use to _⊢_use' 
                ; wkN to wkN' ; wkR to wkR')

   hornC : Type → Type
   hornC (atom A) = atom A
   hornC (A ⊃ B) = hornC B
   hornC (A ∧ B) = hornC A ∧ hornC B
   hornC (□ p A) = □ p (hornC A)
   hornC (■ p A) = ■ p (hornC A)

   hornA : Type → Type
   hornA (atom A) = atom A
   hornA (A ⊃ B) = hornC A ⊃ hornA B
   hornA (A ∧ B) = hornA A ∧ hornA B
   hornA (□ p A) = □ p (hornA A)
   hornA (■ p A) = ■ p (hornA A)

   hornΓ : Ctx → Ctx
   hornΓ [] = [] 
   hornΓ ((A true) :: Γ) = (hornA A true) :: hornΓ Γ 
   hornΓ ((p said A) :: Γ) = (p said hornA A) :: hornΓ Γ
   hornΓ ((p implied A) :: Γ) = (p implied hornA A) :: hornΓ Γ

   pull : ∀{Γ A} → (A true) ∈ Γ → (hornA A true) ∈ hornΓ Γ
   pull {[]} ()
   pull {(A true) :: Γ} Z = Z
   pull {(A true) :: Γ} (S x) = S (pull x)
   pull {(_ said _) :: Γ} (S x) = S (pull x)
   pull {(_ implied _) :: Γ} (S x) = S (pull x)

   mutual
      sem→synu : ∀{A Γ} → Γ ⊢ A use' → hornΓ Γ ⊢ hornA A use
      sem→synu (hyp x) = hyp (pull x)
      sem→synu (⊃E D E) = ⊃E (sem→synu D) (sem→synv E)
      sem→synu (∧E₁ D) = ∧E₁ (sem→synu D)
      sem→synu (∧E₂ D) = ∧E₂ (sem→synu D)

      sem→synv : ∀{A Γ} → Γ ⊢ A verif' → hornΓ Γ ⊢ hornC A verif
      sem→synv (↓↑ D) = {!sem→synu D!}
      sem→synv (⊃I D) = sem→synv D
      sem→synv (∧I D E) = ∧I (sem→synv D) (sem→synv E)
      sem→synv (□I D) = □I (wkN {!!} (sem→synv D))
      sem→synv (□E D E) = □E (sem→synu D) (sem→synv E)
      sem→synv (■I D) = ■I (wkN {!!} (sem→synv D))
      sem→synv (■E D E) = ■E (sem→synu D) (sem→synv E)

   mutual
      syn→semu : ∀{A Γ} → hornΓ Γ ⊢ hornA A use → Γ ⊢ A use'
      syn→semu (hyp x) = hyp {!!}
      syn→semu (⊃E D E) = {!!} -- ⊃E {!D!} {!!}
      syn→semu (∧E₁ D) = {!!}
      syn→semu (∧E₂ D) = {!!}

      syn→semv : ∀{A Γ} → hornΓ Γ ⊢ hornC A verif → Γ ⊢ A verif'
      syn→semv D = {!!}
{-
   sem→syn : ∀{A Γ} → Γ ⇒' A → hornΓ Γ ⇒ hornA A
   sem→syn {A} (init x) = ident (pull x)
   sem→syn (⊃R D) = ⊃R {!sem→syn D!}
   sem→syn (⊃L x D E) = {!!}
   sem→syn (∧R D E) = {!!}
   sem→syn (∧L₁ x D) = {!!}
   sem→syn (∧L₂ x D) = {!!}
   sem→syn (□R D) = {!!}
   sem→syn (□L x D) = {!!}
   sem→syn (■R D) = {!!}
   sem→syn (■L x D) = {!!}



   syn→sem : ∀{A Γ} → hornΓ Γ ⇒ hornC A → Γ ⇒' A
   syn→sem {atom Q} (init x) = init {!x!}
   syn→sem {A ⊃ B} D = ⊃R (syn→sem {B} D)
   syn→sem {A} (⊃L x D E) = ⊃L {!x!} (syn→sem {_} D) (syn→sem {A} E)
   syn→sem {A ∧ B} (∧R D E) = ∧R (syn→sem {A} D) (syn→sem {B} E)
   syn→sem {A} (∧L₁ x D) = ∧L₁ {!x!} (syn→sem D)
   syn→sem (∧L₂ x D) = ∧L₂ {!x!} (syn→sem D)
   syn→sem {□ p A} (□R D) = wkp {!!} (□R (syn→sem D))
   syn→sem (□L x D) = □L {!x!} (syn→sem D)
   syn→sem {■ p A} (■R D) = wkp {!!} (■R (syn→sem D))
   syn→sem (■L x D) = ■L {!!} (syn→sem D)
-}