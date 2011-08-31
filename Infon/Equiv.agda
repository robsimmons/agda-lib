-- Equivalence of sequent calculus, natural deduction, and normal forms

open import Prelude
open import Infon.Core
open import Infon.NatDeduction
open import Infon.Sequent
open import Infon.NormalForms

module Infon.Equiv where

module EQUIV (Prin : Set; _≡?_ : (p q : Prin) → Decidable (p ≡ q)) where

   open CORE Prin _≡?_
   open NAT-DEDUCTION Prin _≡?_ renaming (wk to wkND ; _⊢_ to _⊢_true)
   open SEQUENT Prin _≡?_ renaming (wk' to wkS)
   open NORMAL-FORMS Prin _≡?_ 

   nd→seq : ∀{Γ A} → Γ ⊢ A true → Γ ⇒ A
   nd→seq (hyp x) = ident x
   nd→seq ⊤I = ⊤R
   nd→seq (⊃I D) = ⊃R (nd→seq D)
   nd→seq (⊃E D E) = cut' (nd→seq D) (⊃L Z (wkS sub-wken (nd→seq E)) (ident Z))
   nd→seq (∧I D E) = ∧R (nd→seq D) (nd→seq E)
   nd→seq (∧E₁ D) = cut' (nd→seq D) (∧L₁ Z (ident Z))
   nd→seq (∧E₂ D) = cut' (nd→seq D) (∧L₂ Z (ident Z))
   nd→seq (□I D) = □R (nd→seq D)
   nd→seq (□E D E) = cut' (nd→seq D) (□L Z (wkS sub-wkex (nd→seq E)))
   nd→seq (■I D) = ■R (nd→seq D)
   nd→seq (■E D E) = cut' (nd→seq D) (■L Z (wkS sub-wkex (nd→seq E)))
   
   seq→nf : ∀{Γ A} → Γ ⇒ A → Γ ⊢ A verif
   seq→nf (init x) = ↓↑ (hyp x)
   seq→nf ⊤R = ⊤I
   seq→nf (⊃R D) = ⊃I (seq→nf D)
   seq→nf (⊃L x D E) = substRN [] (⊃E (hyp x) (seq→nf D)) (seq→nf E)
   seq→nf (∧R D E) = ∧I (seq→nf D) (seq→nf E)
   seq→nf (∧L₁ x D) = substRN [] (∧E₁ (hyp x)) (seq→nf D)
   seq→nf (∧L₂ x D) = substRN [] (∧E₂ (hyp x)) (seq→nf D)
   seq→nf (□R D) = □I (seq→nf D)
   seq→nf (□L x D) = □E (hyp x) (seq→nf D)
   seq→nf (■R D) = ■I (seq→nf D)
   seq→nf (■L x D) = ■E (hyp x) (seq→nf D)

   mutual
      verif→nd : ∀{Γ A} → Γ ⊢ A verif → Γ ⊢ A true
      verif→nd (↓↑ D) = use→nd D
      verif→nd ⊤I = ⊤I
      verif→nd (⊃I D) = ⊃I (verif→nd D)
      verif→nd (∧I D E) = ∧I (verif→nd D) (verif→nd E)
      verif→nd (□I D) = □I (verif→nd D)
      verif→nd (□E D E) = □E (use→nd D) (verif→nd E)
      verif→nd (■I D) = ■I (verif→nd D)
      verif→nd (■E D E) = ■E (use→nd D) (verif→nd E)

      use→nd : ∀{Γ A} → Γ ⊢ A use → Γ ⊢ A true
      use→nd (hyp x) = hyp x
      use→nd (⊃E D E) = ⊃E (use→nd D) (verif→nd E)
      use→nd (∧E₁ D) = ∧E₁ (use→nd D)
      use→nd (∧E₂ D) = ∧E₂ (use→nd D)

