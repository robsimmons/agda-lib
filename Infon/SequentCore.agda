-- Sequent Calculus for Full Infon Logic
-- Core: presentation of the calculus and the "easy" lemmas
-- Robert J. Simmons

open import Prelude hiding (⊤)
open import Infon.Core

module Infon.SequentCore where

module SEQUENT-CORE (Prin : Set; _≡?_ : (p q : Prin) → Decidable (p ≡ q)) where

   open CORE Prin _≡?_

   ---------------------------------
   -- Judgmental Full Infon Logic --
   ---------------------------------

   infix 1 _⇒_
   data _⇒_ (Γ : Ctx) : Type → Set where
      init : ∀{A}
         → (x : (atom A true) ∈ Γ)
         → Γ ⇒ atom A
      ⊤R : Γ ⇒ ⊤
      ⊃R : ∀{A B}
         → (D : (A true) :: Γ ⇒ B)
         → Γ ⇒ A ⊃ B
      ⊃L : ∀{A B C}
         → (x : (A ⊃ B true) ∈ Γ)
         → (D : Γ ⇒ A)
         → (E : (B true) :: Γ ⇒ C)
         → Γ ⇒ C
      ∧R : ∀{A B} 
         → (D : Γ ⇒ A)
         → (E : Γ ⇒ B)
         → Γ ⇒ A ∧ B
      ∧L₁ : ∀{A B C}
         → (x : (A ∧ B true) ∈ Γ)
         → (D : (A true) :: Γ ⇒ C)
         → Γ ⇒ C
      ∧L₂ : ∀{A B C}
         → (x : (A ∧ B true) ∈ Γ)
         → (D : (B true) :: Γ ⇒ C)
         → Γ ⇒ C
      □R : ∀{A p} 
         → (D : Γ ○ p ⇒ A)
         → Γ ⇒ □ p A
      □L : ∀{A p C}
         → (x : (□ p A true) ∈ Γ) 
         → (D : (p said A) :: Γ ⇒ C)
         → Γ ⇒ C
      ■R : ∀{A p} 
         → (D : Γ ● p ⇒ A)
         → Γ ⇒ ■ p A
      ■L : ∀{A p C}
         → (x : (■ p A true) ∈ Γ) 
         → (D : (p implied A) :: Γ ⇒ C)
         → Γ ⇒ C



   ----------------------------------------------
   -- Metric (totally nameless representation) --
   ----------------------------------------------

   -- seq captures the shape of sequents
   data seq : Set where
      init : seq
      ⊤R : seq
      ⊃R : (d : seq) → seq 
      ⊃L : (d e : seq) → seq
      ∧R : (d e : seq) → seq
      ∧L₁ : (d : seq) → seq
      ∧L₂ : (d : seq) → seq
      □R : (d : seq) → seq
      □L : (d : seq) → seq
      ■R : (d : seq) → seq
      ■L : (d : seq) → seq

   -- Seq is a equivalent to ⇒, but carries a shape 
   data Seq (Γ : Ctx) : seq → Type → Set where
      init : ∀{A}
         → (x : (atom A true) ∈ Γ)
         → Seq Γ init (atom A)
      ⊤R : Seq Γ ⊤R ⊤
      ⊃R : ∀{A B d}
         → (D : Seq ((A true) :: Γ) d B)
         → Seq Γ (⊃R d) (A ⊃ B)
      ⊃L : ∀{A B C d e}
         → (x : (A ⊃ B true) ∈ Γ)
         → (D : Seq Γ d A)
         → (E : Seq ((B true) :: Γ) e C)
         → Seq Γ (⊃L d e) C
      ∧R : ∀{A B d e} 
         → (D : Seq Γ d A)
         → (E : Seq Γ e B)
         → Seq Γ (∧R d e) (A ∧ B)
      ∧L₁ : ∀{A B C d}
         → (x : (A ∧ B true) ∈ Γ)
         → (D : Seq ((A true) :: Γ) d C)
         → Seq Γ (∧L₁ d) C
      ∧L₂ : ∀{A B C d}
         → (x : (A ∧ B true) ∈ Γ)
         → (D : Seq ((B true) :: Γ) d C)
         → Seq Γ (∧L₂ d) C
      □R : ∀{p A d} 
         → (D : Seq (Γ ○ p) d A)
         → Seq Γ (□R d) (□ p A)
      □L : ∀{p A C d}
         → (x : (□ p A true) ∈ Γ) 
         → (D : Seq ((p said A) :: Γ) d C)
         → Seq Γ (□L d) C
      ■R : ∀{p A d} 
         → (D : Seq (Γ ● p) d A)
         → Seq Γ (■R d) (■ p A)
      ■L : ∀{p A C d}
         → (x : (■ p A true) ∈ Γ) 
         → (D : Seq ((p implied A) :: Γ) d C)
         → Seq Γ (■L d) C
           
   -- Metric erasure
   m→ : ∀{Γ d A} → Seq Γ d A → Γ ⇒ A
   m→ (init x) = init x
   m→ ⊤R = ⊤R
   m→ (⊃R D) = ⊃R (m→ D)
   m→ (⊃L x D E) = ⊃L x (m→ D) (m→ E)
   m→ (∧R D E) = ∧R (m→ D) (m→ E)
   m→ (∧L₁ x D) = ∧L₁ x (m→ D)
   m→ (∧L₂ x D) = ∧L₂ x (m→ D)
   m→ (□R D) = □R (m→ D)
   m→ (□L x D) = □L x (m→ D)
   m→ (■R D) = ■R (m→ D)
   m→ (■L x D) = ■L x (m→ D)
   
   -- Metric calculation
   m : ∀{Γ A} → Γ ⇒ A → seq
   m (init x) = init
   m ⊤R = ⊤R
   m (⊃R D) = ⊃R (m D)
   m (⊃L x D E) = ⊃L (m D) (m E)
   m (∧R D E) = ∧R (m D) (m E)
   m (∧L₁ x D) = ∧L₁ (m D)
   m (∧L₂ x D) = ∧L₂ (m D)
   m (□R D) = □R (m D)
   m (□L x D) = □L (m D)
   m (■R D) = ■R (m D)
   m (■L x D) = ■L (m D)

   -- Metric embedding
   →m : ∀{Γ A} (D : Γ ⇒ A) → Seq Γ (m D) A
   →m (init x) = init x
   →m ⊤R = ⊤R
   →m (⊃R D) = ⊃R (→m D)
   →m (⊃L x D E) = ⊃L x (→m D) (→m E)
   →m (∧R D E) = ∧R (→m D) (→m E)
   →m (∧L₁ x D) = ∧L₁ x (→m D)
   →m (∧L₂ x D) = ∧L₂ x (→m D)
   →m (□R D) = □R (→m D)
   →m (□L x D) = □L x (→m D)
   →m (■R D) = ■R (→m D)
   →m (■L x D) = ■L x (→m D)



   -------------------------
   -- Weakening principle --
   -------------------------

   wk : ∀{Γ Γ' d A} → Γ ⊆ Γ' → Seq Γ d A → Seq Γ' d A
   wk θ (init x) = init (θ x)
   wk θ ⊤R = ⊤R
   wk θ (⊃R D) = ⊃R (wk (sub-cons-congr θ) D)
   wk θ (⊃L x D E) = ⊃L (θ x) (wk θ D) (wk (sub-cons-congr θ) E)
   wk θ (∧R D E) = ∧R (wk θ D) (wk θ E)
   wk θ (∧L₁ x D) = ∧L₁ (θ x) (wk (sub-cons-congr θ) D)
   wk θ (∧L₂ x D) = ∧L₂ (θ x) (wk (sub-cons-congr θ) D)
   wk θ (□R D) = □R (wk (congr○ θ) D)
   wk θ (□L x D) = □L (θ x) (wk (sub-cons-congr θ) D)
   wk θ (■R D) = ■R (wk (congr● θ) D)
   wk θ (■L x D) = ■L (θ x) (wk (sub-cons-congr θ) D)

   wk' : ∀{Γ Γ' A} → Γ ⊆ Γ' → Γ ⇒ A → Γ' ⇒ A
   wk' θ D = m→ (wk θ (→m D))



   ------------------------
   -- Identity principle --
   ------------------------

   ident : ∀{A Γ} → (A true) ∈ Γ → Γ ⇒ A
   ident {atom Q} x = init x
   ident {⊤} x = ⊤R
   ident {A ⊃ B} x = ⊃R (⊃L (S x) (ident Z) (ident Z))
   ident {A ∧ B} x = ∧R (∧L₁ x (ident Z)) (∧L₂ x (ident Z))
   ident {□ p A} {Γ} x = □L x (□R obvious-lemma)
    where
      obvious-lemma : ((p said A) :: Γ) ○ p ⇒ A
      obvious-lemma with p ≡? p
      ... | Inl Refl = ident Z
      ... | Inr contr = abort (contr refl)
   ident {■ p A} {Γ} x = ■L x (■R obvious-lemma) 
    where
      obvious-lemma : ((p implied A) :: Γ) ● p ⇒ A
      obvious-lemma with p ≡? p
      ... | Inl Refl = ident Z
      ... | Inr contr = abort (contr refl)

