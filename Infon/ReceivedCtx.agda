-- Natural Deduction for Full Infon Logic
-- Robert J. Simmons

open import Prelude hiding (⊤)
open import Infon.Core
open import Infon.NatDeduction

module Infon.ReceivedCtx where

module RECEIVED-CTX {Prin} (_≡?_ : (p q : Prin) → Decidable (p ≡ q)) where

   open CORE _≡?_
   open NAT-DEDUCTION _≡?_

    -- In the non-judgmental logic, a context is just a list of types

   Ctx' = List Type



   -- We need to re-define the context clearing operations and their
   -- properties; this way of doing things is noticably less concise and 
   -- convienent than the judgmental style. We don't need quite as much stuff,
   -- though, because we won't be doing any of the metatheory for the received
   -- infon logic directly, just relating it to the judgmental version.

   -- "said" modaility

   _○'_ : Ctx' → Prin → Ctx'
   [] ○' p = []
   (atom Q :: Δ) ○' p = Δ ○' p
   (⊤ :: Δ) ○' p = Δ ○' p
   (A ⊃ B :: Δ) ○' p = Δ ○' p
   (A ∧ B :: Δ) ○' p = Δ ○' p
   (□ q A :: Δ) ○' p with p ≡? q
   (□ .p A :: Δ) ○' p | Inl Refl = A :: Δ ○' p
   ... | Inr _ = Δ ○' p
   (■ q A :: Δ) ○' p = Δ ○' p

   pullR○ : ∀{Δ p A} → □ p A ∈ Δ → A ∈ Δ ○' p
   pullR○ {[]} ()
   pullR○ {atom Q :: Δ} (S x) = pullR○ {Δ} x
   pullR○ {⊤ :: Δ} (S x) = pullR○ {Δ} x
   pullR○ {A ⊃ B :: Δ} (S x) = pullR○ {Δ} x
   pullR○ {A ∧ B :: Δ} (S x) = pullR○ {Δ} x
   pullR○ {□ q A :: Δ} {p} x with p ≡? q
   pullR○ {□ p A :: Δ} Z | Inl Refl = Z
   pullR○ {□ p A :: Δ} (S x) | Inl Refl = S (pullR○ {Δ} x)
   pullR○ {□ q A :: Δ} Z | Inr contr = abort (contr refl)
   pullR○ {□ q A :: Δ} (S x) | Inr _ = pullR○ {Δ} x
   pullR○ {■ q A :: Δ} (S x) = pullR○ {Δ} x

   congrR○ : ∀{Δ p Δ'} → Δ ⊆ Δ' → (Δ ○' p) ⊆ (Δ' ○' p)
   congrR○ {[]} θ ()
   congrR○ {atom Q :: Δ} θ x = congrR○ {Δ} (θ o sub-cons) x
   congrR○ {⊤ :: Δ} θ x = congrR○ {Δ} (θ o sub-cons) x
   congrR○ {A ⊃ B :: Δ} θ x = congrR○ {Δ} (θ o sub-cons) x
   congrR○ {A ∧ B :: Δ} θ x = congrR○ {Δ} (θ o sub-cons) x
   congrR○ {□ q A :: Δ} {p} θ x with p ≡? q 
   congrR○ {□ .p A :: Δ} {p} θ Z | Inl Refl = pullR○ (θ Z)
   congrR○ {□ .p A :: Δ} {p} θ (S x) | Inl Refl = congrR○ {Δ} (θ o sub-cons) x
   congrR○ {□ q A :: Δ} {p} θ x | Inr _ = congrR○ {Δ} (θ o sub-cons) x
   congrR○ {■ q A :: Δ} {p} θ x = congrR○ {Δ} (θ o sub-cons) x 

   -- "implied" modality

   _●'_ : Ctx' → Prin → Ctx'
   [] ●' p = []
   (atom Q :: Δ) ●' p = Δ ●' p
   (⊤ :: Δ) ●' p = Δ ●' p
   (A ⊃ B :: Δ) ●' p = Δ ●' p
   (A ∧ B :: Δ) ●' p = Δ ●' p
   (□ q A :: Δ) ●' p with p ≡? q
   (□ .p A :: Δ) ●' p | Inl Refl = A :: Δ ●' p
   ... | Inr _ = Δ ●' p
   (■ q A :: Δ) ●' p with p ≡? q
   (■ .p A :: Δ) ●' p | Inl Refl = A :: Δ ●' p
   ... | Inr _ = Δ ●' p

   pullR● : ∀{Δ p A} → □ p A ∈ Δ → A ∈ Δ ●' p
   pullR● {[]} ()
   pullR● {atom Q :: Δ} (S x) = pullR● {Δ} x
   pullR● {⊤ :: Δ} (S x) = pullR● {Δ} x
   pullR● {A ⊃ B :: Δ} (S x) = pullR● {Δ} x
   pullR● {A ∧ B :: Δ} (S x) = pullR● {Δ} x
   pullR● {□ q A :: Δ} {p} x with p ≡? q
   pullR● {□ p A :: Δ} Z | Inl Refl = Z
   pullR● {□ p A :: Δ} (S x) | Inl Refl = S (pullR● {Δ} x)
   pullR● {□ p A :: Δ} Z | Inr contr = abort (contr refl)
   pullR● {□ q A :: Δ} (S x) | Inr _ = pullR● {Δ} x
   pullR● {■ q A :: Δ} {p} x with p ≡? q
   pullR● {■ p A :: Δ} (S x) | Inl Refl = S (pullR● {Δ} x) -- S (pullR● {Δ} x)
   pullR● {■ q A :: Δ} (S x) | Inr _ = pullR● {Δ} x

   pullR●' : ∀{Δ p A} → ■ p A ∈ Δ → A ∈ Δ ●' p
   pullR●' {[]} ()
   pullR●' {atom Q :: Δ} (S x) = pullR●' {Δ} x
   pullR●' {⊤ :: Δ} (S x) = pullR●' {Δ} x
   pullR●' {A ⊃ B :: Δ} (S x) = pullR●' {Δ} x
   pullR●' {A ∧ B :: Δ} (S x) = pullR●' {Δ} x
   pullR●' {□ q A :: Δ} {p} x with p ≡? q
   pullR●' {□ p A :: Δ} (S x) | Inl Refl = S (pullR●' {Δ} x)
   pullR●' {□ q A :: Δ} (S x) | Inr _ = pullR●' {Δ} x
   pullR●' {■ q A :: Δ} {p} x with p ≡? q
   pullR●' {■ p A :: Δ} Z | Inl Refl = Z
   pullR●' {■ p A :: Δ} (S x) | Inl Refl = S (pullR●' {Δ} x)
   pullR●' {■ p A :: Δ} Z | Inr contr = abort (contr refl)
   pullR●' {■ q A :: Δ} (S x) | Inr _ = pullR●' {Δ} x

   congrR● : ∀{Δ p Δ'} → Δ ⊆ Δ' → (Δ ●' p) ⊆ (Δ' ●' p)
   congrR● {[]} θ ()
   congrR● {atom Q :: Δ} θ x = congrR● {Δ} (θ o sub-cons) x
   congrR● {⊤ :: Δ} θ x = congrR● {Δ} (θ o sub-cons) x
   congrR● {A ⊃ B :: Δ} θ x = congrR● {Δ} (θ o sub-cons) x
   congrR● {A ∧ B :: Δ} θ x = congrR● {Δ} (θ o sub-cons) x
   congrR● {□ q A :: Δ} {p} θ x with p ≡? q 
   congrR● {□ p A :: Δ} θ Z | Inl Refl = pullR● (θ Z)
   congrR● {□ p A :: Δ} θ (S x) | Inl Refl = congrR● {Δ} (θ o sub-cons) x
   congrR● {□ q A :: Δ} θ x | Inr _ = congrR● {Δ} (θ o sub-cons) x
   congrR● {■ q A :: Δ} {p} θ x with p ≡? q
   congrR● {■ p A :: Δ} θ Z | Inl Refl = pullR●' (θ Z) 
   congrR● {■ p A :: Δ} θ (S x) | Inl Refl = congrR● {Δ} (θ o sub-cons) x 
   congrR● {■ p A :: Δ} θ x | Inr _ = congrR● {Δ} (θ o sub-cons) x



   -- The context erasure operation takes a judgmental context and turns
   -- it into a non-judgmental context by turning judgmental forms
   -- (i.e. p says A) back into propositional forms (□ p A).

   _⁻ : Ctx → Ctx' 
   [] ⁻ = []
   ((A true) :: Γ) ⁻ = A :: Γ ⁻
   ((p said A) :: Γ) ⁻ = □ p A :: Γ ⁻
   ((p implied A) :: Γ) ⁻ = ■ p A :: Γ ⁻
 
   -- We can "pull" variables through the erasure operation in both 
   -- directions. We always know what the a judgmental variable will become
   -- because the erasure operation is finite.

   pull : ∀{Γ A} → (A true) ∈ Γ → A ∈ Γ ⁻
   pull {[]} ()
   pull {(A true) :: Γ} Z = Z
   pull {(_ true) :: Γ} (S x) = S (pull x)
   pull {(_ said _) :: Γ} (S x) = S (pull x)
   pull {(_ implied _) :: Γ} (S x) = S (pull x)

   pull□ : ∀{Γ p A} → (p said A) ∈ Γ → A ∈ (Γ ○ p) ⁻
   pull□ {[]} ()
   pull□ {(_ true) :: Γ} (S x) = pull□ x
   pull□ {(q said A) :: Γ} {p} x with p ≡? q
   pull□ {(p said A) :: Γ} Z | Inl Refl = Z
   pull□ {(p said A) :: Γ} (S x) | Inl Refl = S (pull□ x)
   pull□ {(q said A) :: Γ} Z | Inr contr = abort (contr refl)
   pull□ {(q said A) :: Γ} (S x) | Inr _ = pull□ x
   pull□ {(_ implied _) :: Γ} (S x) = pull□ x

   pull■ : ∀{Γ p A} → (p said A) ∈ Γ → A ∈ (Γ ● p) ⁻
   pull■ {[]} ()
   pull■ {(_ true) :: Γ} (S x) = pull■ x
   pull■ {(q said A) :: Γ} {p} x with p ≡? q
   pull■ {(p said A) :: Γ} Z | Inl Refl = Z
   pull■ {(p said A) :: Γ} (S x) | Inl Refl = S (pull■ x)
   pull■ {(q said A) :: Γ} Z | Inr contr = abort (contr refl)
   pull■ {(q said A) :: Γ} (S x) | Inr _ = pull■ x
   pull■ {(q implied A) :: Γ} {p} (S x) with p ≡? q
   pull■ {(p implied A) :: Γ} (S x) | Inl Refl = S (pull■ x) -- pull■ x
   pull■ {(q implied A) :: Γ} (S x) | Inr _ = pull■ x -- pull■ x

   pull■' : ∀{Γ p A} → (p implied A) ∈ Γ → A ∈ (Γ ● p) ⁻
   pull■' {[]} ()
   pull■' {(_ true) :: Γ} (S x) = pull■' x
   pull■' {(q said A) :: Γ} {p} x with p ≡? q
   pull■' {(p said A) :: Γ} (S x) | Inl Refl = S (pull■' x)
   pull■' {(q said A) :: Γ} (S x) | Inr _ = pull■' x
   pull■' {(q implied A) :: Γ} {p} x with p ≡? q
   pull■' {(p implied A) :: Γ} Z | Inl Refl = Z 
   pull■' {(p implied A) :: Γ} (S x) | Inl Refl = S (pull■' x)
   pull■' {(p implied A) :: Γ} Z | Inr contr = abort (contr refl)
   pull■' {(p implied A) :: Γ} (S x) | Inr _ = pull■' x

   -- When we pull an object from the erased context into the judgmental 
   -- context, we don't know whether a proposition like □ p A will turn
   -- into the judgmental form (□ p A) true or the judgmental form
   -- p said A. The A ∈⁻ Γ shorthand captures the disjunctive possibilites.

   _∈⁻_ : Type → Ctx → Set
   _∈⁻_ A Γ = ((A true) ∈ Γ)
        + ((∃ λ p → ∃ λ B → (A ≡ □ p B) × ((p said B) ∈ Γ))
        + (∃ λ p → ∃ λ B → (A ≡ ■ p B) × ((p implied B) ∈ Γ)))

   S⁻ : ∀{J Γ A} → A ∈⁻ Γ → A ∈⁻ (J :: Γ)
   S⁻ (Inl x) = Inl (S x)
   S⁻ (Inr (Inl (p , A , Refl , x))) = Inr (Inl (p , A , refl , S x))  
   S⁻ (Inr (Inr (p , A , Refl , x))) = Inr (Inr (p , A , refl , S x))  

   pull⁻ : ∀{Γ A} → A ∈ Γ ⁻ → A ∈⁻ Γ
   pull⁻ {[]} ()
   pull⁻ {(A true) :: Γ} Z = Inl Z
   pull⁻ {(p said A) :: Γ} Z = Inr (Inl (p , A , refl , Z))
   pull⁻ {(p implied A) :: Γ} Z = Inr (Inr (p , A , refl , Z))
   pull⁻ {(_ true) :: Γ} (S n) = S⁻ (pull⁻ n) 
   pull⁻ {(_ said _) :: Γ} (S n) = S⁻ (pull⁻ n)
   pull⁻ {(_ implied _) :: Γ} (S n) = S⁻ (pull⁻ n)



   -- The "reverse" of the erasure operation is the operation that scans the
   -- context for anything with a certain judgmental form, and then gives
   -- the judgmental form: for instance, scanning for (□ p A true) to produce
   -- p said A. 

   -- The need for this is partially an artifact of our translation, since
   -- we perform eliminations at the "last possible moment" (loking at proofs 
   -- bottom-up)

   -- "said" modality

   infix 30 _○⁺_
   _○⁺_ : Ctx → Prin → Ctx 
   [] ○⁺ p = []
   ((atom Q true) :: Γ) ○⁺ p = Γ ○⁺ p
   ((⊤ true) :: Γ) ○⁺ p = Γ ○⁺ p
   ((A ⊃ B true) :: Γ) ○⁺ p = Γ ○⁺ p
   ((A ∧ B true) :: Γ) ○⁺ p = Γ ○⁺ p
   ((□ q A true) :: Γ) ○⁺ p with p ≡? q
   ((□ .p A true) :: Γ) ○⁺ p | Inl Refl = (p said A) :: Γ ○⁺ p
   ((□ q A true) :: Γ) ○⁺ p | Inr _ = Γ ○⁺ p
   ((■ q A true) :: Γ) ○⁺ p = Γ ○⁺ p
   ((_ said _) :: Γ) ○⁺ p = Γ ○⁺ p
   ((_ implied _) :: Γ) ○⁺ p = Γ ○⁺ p

   pull○⁺ : ∀{Γ p A} → (□ p A true) ∈ Γ → (A true) ∈ ((Γ ○⁺ p) ○ p)
   pull○⁺ {[]} ()
   pull○⁺ {(atom Q true) :: Γ} (S x) = pull○⁺ {Γ} x
   pull○⁺ {(⊤ true) :: Γ} (S x) = pull○⁺ {Γ} x
   pull○⁺ {(A ⊃ B true) :: Γ} (S x) = pull○⁺ {Γ} x
   pull○⁺ {(A ∧ B true) :: Γ} (S x) = pull○⁺ {Γ} x
   pull○⁺ {(□ q A true) :: Γ} {p} x with p ≡? q
   pull○⁺ {(□ p A true) :: Γ} x | Inl Refl with p ≡? p -- That's bogus, Agda.
   pull○⁺ {(□ p A true) :: Γ} Z | Inl Refl | Inl Refl = Z
   pull○⁺ {(□ p A true) :: Γ} (S x) | Inl Refl | Inl Refl = S (pull○⁺ {Γ} x)
   pull○⁺ {(□ p A true) :: Γ} x | Inl Refl | Inr contr = abort (contr refl)
   pull○⁺ {(□ p A true) :: Γ} Z | Inr contr = abort (contr refl) -- 
   pull○⁺ {(□ p A true) :: Γ} (S x) | Inr _ = pull○⁺ {Γ} x
   pull○⁺ {(■ q A true) :: Γ} (S x) = pull○⁺ {Γ} x
   pull○⁺ {(q said A) :: Γ} (S x) = pull○⁺ {Γ} x
   pull○⁺ {(q implied A) :: Γ} (S x) = pull○⁺ {Γ} x

   sub○⁺ : ∀{Γ p} (Δ : Ctx') → Δ ⊆ Γ ⁻ → (Δ ○' p) ⊆ ((Γ ○⁺ p ++ Γ) ○ p) ⁻
   sub○⁺ [] θ ()
   sub○⁺ {Γ} (atom Q :: Δ) θ x = sub○⁺ {Γ} Δ (θ o S) x
   sub○⁺ {Γ} (⊤ :: Δ) θ x = sub○⁺ {Γ} Δ (θ o S) x
   sub○⁺ {Γ} (A ⊃ B :: Δ) θ x = sub○⁺ {Γ} Δ (θ o S) x
   sub○⁺ {Γ} (A ∧ B :: Δ) θ x = sub○⁺ {Γ} Δ (θ o S) x
   sub○⁺ {Γ} {p} (□ q A :: Δ) θ x with p ≡? q 
   sub○⁺ {Γ} (□ p A :: Δ) θ Z | Inl Refl with pull⁻ {Γ} (θ Z)
   ... | Inl x = pull (sub-eq (ID.symm (hmorph○ (Γ ○⁺ p))) 
                   (LIST.in-append (pull○⁺ x) (Γ ○ p)))
   ... | Inr (Inl (.p , .A , Refl , x)) = pull□ (LIST.append-in (Γ ○⁺ p) x)
   ... | Inr (Inr (_ , _ , () , _))
   sub○⁺ {Γ} (□ p A :: Δ) θ (S x) | Inl Refl = sub○⁺ {Γ} Δ (θ o S) x
   sub○⁺ {Γ} (□ q A :: Δ) θ x | Inr _ = sub○⁺ {Γ} Δ (θ o S) x
   sub○⁺ {Γ} (■ q A :: Δ) θ x = sub○⁺ {Γ} Δ (θ o S) x

   -- "implied" modality

   infix 30 _●⁺_
   _●⁺_ : Ctx → Prin → Ctx 
   [] ●⁺ p = []
   ((atom Q true) :: Γ) ●⁺ p = Γ ●⁺ p
   ((⊤ true) :: Γ) ●⁺ p = Γ ●⁺ p
   ((A ⊃ B true) :: Γ) ●⁺ p = Γ ●⁺ p
   ((A ∧ B true) :: Γ) ●⁺ p = Γ ●⁺ p
   ((□ q A true) :: Γ) ●⁺ p with p ≡? q
   ((□ .p A true) :: Γ) ●⁺ p | Inl Refl = (p said A) :: Γ ●⁺ p
   ((□ q A true) :: Γ) ●⁺ p | Inr _ = Γ ●⁺ p
   ((■ q A true) :: Γ) ●⁺ p with p ≡? q
   ((■ .p A true) :: Γ) ●⁺ p | Inl Refl = (p implied A) :: Γ ●⁺ p
   ((■ q A true) :: Γ) ●⁺ p | Inr _ = Γ ●⁺ p
   ((_ said _) :: Γ) ●⁺ p = Γ ●⁺ p
   ((_ implied _) :: Γ) ●⁺ p = Γ ●⁺ p

   pull●⁺ : ∀{Γ p A} → (□ p A true) ∈ Γ → (A true) ∈ ((Γ ●⁺ p) ● p)
   pull●⁺ {[]} ()
   pull●⁺ {(atom Q true) :: Γ} (S x) = pull●⁺ {Γ} x
   pull●⁺ {(⊤ true) :: Γ} (S x) = pull●⁺ {Γ} x
   pull●⁺ {(A ⊃ B true) :: Γ} (S x) = pull●⁺ {Γ} x
   pull●⁺ {(A ∧ B true) :: Γ} (S x) = pull●⁺ {Γ} x
   pull●⁺ {(□ q A true) :: Γ} {p} x with p ≡? q
   pull●⁺ {(□ p A true) :: Γ} x | Inl Refl with p ≡? p -- That's bogus, Agda.
   pull●⁺ {(□ p A true) :: Γ} Z | Inl Refl | Inl Refl = Z
   pull●⁺ {(□ p A true) :: Γ} (S x) | Inl Refl | Inl Refl = S (pull●⁺ {Γ} x)
   pull●⁺ {(□ p A true) :: Γ} x | Inl Refl | Inr contr = abort (contr refl)
   pull●⁺ {(□ p A true) :: Γ} Z | Inr contr = abort (contr refl) -- 
   pull●⁺ {(□ p A true) :: Γ} (S x) | Inr _ = pull●⁺ {Γ} x
   pull●⁺ {(■ q A true) :: Γ} {p} x with p ≡? q
   pull●⁺ {(■ p A true) :: Γ} x | Inl Refl with p ≡? p -- That's bogus, Agda.
   pull●⁺ {(■ p A true) :: Γ} (S x) | Inl Refl | Inl Refl = S (pull●⁺ {Γ} x)
   pull●⁺ {(■ p A true) :: Γ} x | Inl Refl | Inr contr = abort (contr refl)
   pull●⁺ {(■ p A true) :: Γ} (S x) | Inr _ = pull●⁺ {Γ} x
   pull●⁺ {(q said A) :: Γ} (S x) = pull●⁺ {Γ} x
   pull●⁺ {(q implied A) :: Γ} (S x) = pull●⁺ {Γ} x

   pull●⁺' : ∀{Γ p A} → (■ p A true) ∈ Γ → (A true) ∈ ((Γ ●⁺ p) ● p)
   pull●⁺' {[]} ()
   pull●⁺' {(atom Q true) :: Γ} (S x) = pull●⁺' {Γ} x
   pull●⁺' {(⊤ true) :: Γ} (S x) = pull●⁺' {Γ} x
   pull●⁺' {(A ⊃ B true) :: Γ} (S x) = pull●⁺' {Γ} x
   pull●⁺' {(A ∧ B true) :: Γ} (S x) = pull●⁺' {Γ} x
   pull●⁺' {(□ q A true) :: Γ} {p} x with p ≡? q
   pull●⁺' {(□ p A true) :: Γ} x | Inl Refl with p ≡? p -- That's bogus, Agda.
   pull●⁺' {(□ p A true) :: Γ} (S x) | Inl Refl | Inl Refl = S (pull●⁺' {Γ} x)
   pull●⁺' {(□ p A true) :: Γ} x | Inl Refl | Inr contr = abort (contr refl)
   pull●⁺' {(□ q A true) :: Γ} (S x) | Inr _ = pull●⁺' {Γ} x
   pull●⁺' {(■ q A true) :: Γ} {p} x with p ≡? q
   pull●⁺' {(■ p A true) :: Γ} x | Inl Refl with p ≡? p -- That's bogus, Agda.
   pull●⁺' {(■ p A true) :: Γ} Z | Inl Refl | Inl Refl = Z
   pull●⁺' {(■ p A true) :: Γ} (S x) | Inl Refl | Inl Refl = S (pull●⁺' {Γ} x)
   pull●⁺' {(■ p A true) :: Γ} x | Inl Refl | Inr contr = abort (contr refl)
   pull●⁺' {(■ p A true) :: Γ} Z | Inr contr = abort (contr refl)
   pull●⁺' {(■ q A true) :: Γ} (S x) | Inr _ = pull●⁺' {Γ} x
   pull●⁺' {(q said A) :: Γ} (S x) = pull●⁺' {Γ} x
   pull●⁺' {(q implied A) :: Γ} (S x) = pull●⁺' {Γ} x

   sub●⁺ : ∀{Γ p} (Δ : Ctx') → Δ ⊆ Γ ⁻ → (Δ ●' p) ⊆ ((Γ ●⁺ p ++ Γ) ● p) ⁻
   sub●⁺ [] θ ()
   sub●⁺ {Γ} (atom Q :: Δ) θ x = sub●⁺ {Γ} Δ (θ o S) x
   sub●⁺ {Γ} (⊤ :: Δ) θ x = sub●⁺ {Γ} Δ (θ o S) x
   sub●⁺ {Γ} (A ⊃ B :: Δ) θ x = sub●⁺ {Γ} Δ (θ o S) x
   sub●⁺ {Γ} (A ∧ B :: Δ) θ x = sub●⁺ {Γ} Δ (θ o S) x
   sub●⁺ {Γ} {p} (□ q A :: Δ) θ x with p ≡? q 
   sub●⁺ {Γ} (□ p A :: Δ) θ Z | Inl Refl with pull⁻ {Γ} (θ Z)
   ... | Inl x = pull (sub-eq (ID.symm (hmorph● (Γ ●⁺ p))) 
                   (LIST.in-append (pull●⁺ x) (Γ ● p)))
   ... | Inr (Inl (.p , .A , Refl , x)) = pull■ (LIST.append-in (Γ ●⁺ p) x)
   ... | Inr (Inr (_ , _ , () , _))
   sub●⁺ {Γ} (□ p A :: Δ) θ (S x) | Inl Refl = sub●⁺ {Γ} Δ (θ o S) x
   sub●⁺ {Γ} (□ q A :: Δ) θ x | Inr _ = sub●⁺ {Γ} Δ (θ o S) x
   sub●⁺ {Γ} {p} (■ q A :: Δ) θ x with p ≡? q
   sub●⁺ {Γ} (■ p A :: Δ) θ Z | Inl Refl with pull⁻ {Γ} (θ Z)
   ... | Inl x = pull (sub-eq (ID.symm (hmorph● (Γ ●⁺ p)))
                   (LIST.in-append (pull●⁺' x) (Γ ● p)))
   ... | Inr (Inl (_ , _ , () , _)) 
   ... | Inr (Inr (.p , .A , Refl , x)) = pull■' (LIST.append-in (Γ ●⁺ p) x)
   sub●⁺ {Γ} (■ p A :: Δ) θ (S x) | Inl Refl = sub●⁺ {Γ} Δ (θ o S) x
   sub●⁺ {Γ} (■ q A :: Δ) θ x | Inr _ = sub●⁺ {Γ} Δ (θ o S) x 

