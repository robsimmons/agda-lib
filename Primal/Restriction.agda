-- A syntactic account of Primal Infon Logic

open import Prelude
open import Infon.Core
import Infon.Sequent
import Primal.Sequent
open import Primal.Sound

module Primal.Restriction where

module RESTRICTION {Prin : Set} (_≡?_ : (p q : Prin) → Decidable (p ≡ q)) where

   open CORE _≡?_
   open SOUND _≡?_
   open Infon.Sequent.SEQUENT _≡?_ 
      hiding (cut□ ; cut□' ; cut■ ; cut■')
   open Primal.Sequent.SEQUENT _≡?_ 
      hiding (cut□ ; cut□' ; cut■ ; cut■')
      renaming (cut to cutp ; cut' to cutp'
                ; wk to wkp ; wk' to wkp' ; _⇒_ to _⇒'_ 
                ; m→ to m→' ; →m to →m'
                ; Seq to Seq')

   -- Describing the erasure of context down to Horn clauses. 

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



   -- Pulling variables back and forth across the translation barriar

   push : ∀{Γ A} 
      → (A true) ∈ hornΓ Γ 
      → ∃ λ B → (A ≡ hornA B) × ((B true) ∈ Γ)
   push {[]} ()
   push {(A true) :: Γ} Z = A , refl , Z
   push {(A true) :: Γ} (S x) with push {Γ} x
   ... | (B , Refl , y) = B , refl , S y
   push {(_ said _) :: Γ} (S x) with push {Γ} x
   ... | (B , Refl , y) = B , refl , S y
   push {(_ implied _) :: Γ} (S x) with push {Γ} x
   ... | (B , Refl , y) = B , refl , S y

   pull : ∀{Γ A} → (A true) ∈ Γ → (hornA A true) ∈ hornΓ Γ
   pull {[]} ()
   pull {(A true) :: Γ} Z = Z
   pull {(A true) :: Γ} (S x) = S (pull x)
   pull {(_ said _) :: Γ} (S x) = S (pull x)
   pull {(_ implied _) :: Γ} (S x) = S (pull x)



   -- Syntax To Semantics: If we can prove syntatically restricted sequent
   -- (hornΓ Γ) ⇒ (hornC A) in full infon logic, then we can prove the 
   -- unrestricted sequent (Γ ⇒ A) in the semantically restricted primal
   -- infon logic. 

   horn○ : ∀{p} (Γ : Ctx) → ((hornΓ Γ) ○ p) ⊆ (hornΓ (Γ ○ p))
   horn○ [] = λ ()
   horn○ ((A true) :: Γ) = horn○ Γ
   horn○ {p} ((q said A) :: Γ) with p ≡? q 
   horn○ ((p said A) :: Γ) | Inl Refl = sub-cons-congr (horn○ Γ)
   horn○ ((q said A) :: Γ) | Inr _ = horn○ Γ
   horn○ ((q implied A) :: Γ) = horn○ Γ

   horn●₁ : ∀{p} (Γ : Ctx) → ((hornΓ Γ) ● p) ⊆ (hornΓ (Γ ● p))
   horn●₁ [] = λ ()
   horn●₁ ((A true) :: Γ) = horn●₁ Γ
   horn●₁ {p} ((q said A) :: Γ) with p ≡? q 
   horn●₁ ((p said A) :: Γ) | Inl Refl = sub-cons-congr (horn●₁ Γ)
   horn●₁ ((q said A) :: Γ) | Inr _ = horn●₁ Γ
   horn●₁ {p} ((q implied A) :: Γ) with p ≡? q 
   horn●₁ ((p implied A) :: Γ) | Inl Refl = sub-cons-congr (horn●₁ Γ)
   horn●₁ ((q implied A) :: Γ) | Inr _ = horn●₁ Γ

   syn→sem' : ∀{Γ d} → (A : Type) → Seq (hornΓ Γ) d (hornC A) → Γ ⇒' A
   syn→sem' {Γ} (atom Q) (init x) with push {Γ} {atom Q} x
   ... | (atom .Q , Refl , y) = init y
   ... | (_ ⊃ _ , () , _)
   ... | (_ ∧ _ , () , _)
   ... | (□ _ _ , () , _)
   ... | (■ _ _ , () , _)

   syn→sem' (A ⊃ B) D = ⊃R (syn→sem' B D) 
   syn→sem' {Γ} A (⊃L x D E) with push {Γ} {_} x
   ... | (atom _ , () , _)
   ... | (B ⊃ C , Refl , y) = ⊃L y (syn→sem' B D) (syn→sem' A E)
   ... | (_ ∧ _ , () , _) 
   ... | (□ _ _ , () , _)
   ... | (■ _ _ , () , _)

   syn→sem' (A ∧ B) (∧R D E) = ∧R (syn→sem' A D) (syn→sem' B E)
   syn→sem' {Γ} A (∧L₁ x D) with push {Γ} {_} x
   ... | (atom _ , () , _)
   ... | (_ ⊃ _ , () , _)
   ... | (B ∧ C , Refl , y) = ∧L₁ y (syn→sem' A D) 
   ... | (□ _ _ , () , _)
   ... | (■ _ _ , () , _)
   syn→sem' {Γ} A (∧L₂ x D) with push {Γ} {_} x
   ... | (atom _ , () , _)
   ... | (_ ⊃ _ , () , _)
   ... | (B ∧ C , Refl , y) = ∧L₂ y (syn→sem' A D) 
   ... | (□ _ _ , () , _)
   ... | (■ _ _ , () , _)

   syn→sem' {Γ} (□ p A) (□R D) = □R (syn→sem' A (wk (horn○ Γ) D))
   syn→sem' {Γ} A (□L x D) with push {Γ} {_} x
   ... | (atom _ , () , _)
   ... | (_ ⊃ _ , () , _)
   ... | (_ ∧ _ , () , _) 
   ... | (□ p B , Refl , y) = □L y (syn→sem' A D)
   ... | (■ _ _ , () , _)

   syn→sem' {Γ} (■ p A) (■R D) = ■R (syn→sem' A (wk (horn●₁ Γ) D))
   syn→sem' {Γ} A (■L x D) with push {Γ} {_} x
   ... | (atom _ , () , _)
   ... | (_ ⊃ _ , () , _)
   ... | (_ ∧ _ , () , _) 
   ... | (□ _ _ , () , _)
   ... | (■ p B , Refl , y) = ■L y (syn→sem' A D)

   syn→sem : ∀{Γ A} → hornΓ Γ ⇒ hornC A → Γ ⇒' A
   syn→sem D = syn→sem' _ (→m D)

   -- As a corollary, the truth of the Horn erasure of a sequent implies
   -- the truth of the sequent. 

   erasure-sound : ∀{Γ A} → hornΓ Γ ⇒ hornC A → Γ ⇒ A
   erasure-sound D = sound (syn→sem D)



   -- 

   horn○₂ : ∀{p} (Γ : Ctx) → (hornΓ (Γ ○ p)) ⊆ ((hornΓ Γ) ○ p)
   horn○₂ Γ = {!!}

   horn●₂ : ∀{p} (Γ : Ctx) → (hornΓ (Γ ● p)) ⊆ ((hornΓ Γ) ● p)
   horn●₂ Γ = {!!}

   -- It's not an identity theorem, but it's identity theorish

   identty : ∀{Γ} (A : Type) → (hornC A true) ∈ Γ → Γ ⇒' hornA A
   identty (atom Q) x = init x
   identty (A ⊃ B) x = ⊃R (identty B x)
   identty (A ∧ B) x = ∧L₁ x (∧L₂ (S x) (∧R (identty A (S Z)) (identty B Z)))
   identty {Γ} (□ p A) x = □L x (□R D)
    where 
      D : ((p said hornC A) :: Γ) ○ p ⇒' hornA A 
      D with p ≡? p  
      ... | Inl Refl = identty A Z 
      ... | Inr contr = abort (contr refl) 
   identty {Γ} (■ p A) x = ■L x (■R D)
    where 
      D : ((p implied hornC A) :: Γ) ● p ⇒' hornA A 
      D with p ≡? p  
      ... | Inl Refl = identty A Z 
      ... | Inr contr = abort (contr refl) 

   weaken-right' : ∀{d} (Γ : Ctx) (A : Type) 
         → Seq' (hornΓ Γ) d (hornC A)
         → hornΓ Γ ⇒' hornA A
   weaken-right' Γ (A ⊃ B) D = ⊃R (weaken-right' Γ B D)
   weaken-right' Γ (A ∧ B) (∧R D E) = 
      ∧R (weaken-right' Γ A D) (weaken-right' Γ B E)
   weaken-right' Γ (CORE.□ p A) (□R D) = 
         □R (wkp' (horn○₂ Γ) (weaken-right' (Γ ○ p) A (wkp (horn○ Γ) D)))
   weaken-right' Γ (CORE.■ p A) (■R D) = 
         ■R (wkp' (horn●₂ Γ) (weaken-right' (Γ ● p) A (wkp (horn●₁ Γ) D)))
   
   weaken-right' Γ A (init x) = identty A x 
   weaken-right' Γ A (⊃L x D E) with push {Γ} x
   ... | (atom _ , () , _)
   ... | (B ⊃ C , Refl , y) = ⊃L x (m→' D) (weaken-right' ((C true) :: Γ) A E)
   ... | (_ ∧ _ , () , _) 
   ... | (□ _ _ , () , _) 
   ... | (■ _ _ , () , _)

   weaken-right' Γ A (∧L₁ x D) with push {Γ} x
   ... | (atom _ , () , _)
   ... | (_ ⊃ _ , () , _)
   ... | (B ∧ C , Refl , _) = ∧L₁ x (weaken-right' ((B true) :: Γ) A D)
   ... | (□ _ _ , () , _) 
   ... | (■ _ _ , () , _)

   weaken-right' Γ A (∧L₂ x D) with push {Γ} x
   ... | (atom _ , () , _)
   ... | (_ ⊃ _ , () , _)
   ... | (B ∧ C , Refl , _) = ∧L₂ x (weaken-right' ((C true) :: Γ) A D)
   ... | (□ _ _ , () , _)  
   ... | (■ _ _ , () , _)

   weaken-right' Γ A (□L x D) with push {Γ} x
   ... | (atom _ , () , _)
   ... | (_ ⊃ _ , () , _)
   ... | (_ ∧ _ , () , _) 
   ... | (□ p B , Refl , _) = □L x (weaken-right' ((p said B) :: Γ) A D)
   ... | (■ _ _ , () , _)

   weaken-right' Γ A (■L x D) with push {Γ} x
   ... | (atom _ , () , _)
   ... | (_ ⊃ _ , () , _)
   ... | (_ ∧ _ , () , _) 
   ... | (□ _ _ , () , _) 
   ... | (■ p B , Refl , _) = ■L x (weaken-right' ((p implied B) :: Γ) A D)
 
   weaken-right : ∀{A} (Γ : Ctx) 
      → hornΓ Γ ⇒' hornC A
      → hornΓ Γ ⇒' hornA A
   weaken-right Γ D = weaken-right' Γ _ (→m' D)

   counter : (atom "a" ⊃ (atom "b" ⊃ atom "c") true) 
        :: (atom "a" true) 
        :: []
        ⇒' atom "b" ⊃ atom "c"
   counter = ⊃L Z (init (S Z)) (init Z)

   pf : (atom "a" ⊃ atom "b" true) 
        :: ((atom "a" ⊃ atom "b") ⊃ (atom "c" ⊃ (atom "d" ⊃ atom "e")) true)
        :: (atom "c" true) 
        :: []
        ⇒' atom "d" ⊃ atom "e"
   pf = ⊃L (S Z) (init Z) (⊃L Z (init (S (S (S Z)))) (init Z))

   syn' : ∀{Γ A} → Γ ⇒' A → hornΓ Γ ⇒' hornA A
   syn' (init x) = init (pull x)
   syn' (⊃R D) = ⊃R (syn' D) -- ⊃R (syn' D)
   syn' (⊃L x D E) = ⊃L (pull x) {!syn' D!} {!!} -- ⊃L (pull x) {!syn' D!} {!syn' E!}
   syn' (∧R D E) = {!!}
   syn' (∧L₁ x D) = {!!}
   syn' (∧L₂ x D) = {!!}
   syn' (□R D) = {!!}
   syn' (□L x D) = {!!}
   syn' (■R D) = {!!}
   syn' (■L x D) = {!!}



   righty : (Γ : Ctx) (A : Type) 
         → hornΓ Γ ⇒' hornA A
         → hornΓ Γ ⇒' hornC A
   righty Γ (A ⊃ B) D = {!!}
   righty Γ (A ∧ B) (∧R D E) = {!!}
   righty Γ (□ p A) D = {!!}
   righty Γ (■ p A) D = {!!}
   righty Γ A (init x) = {!x!}
   righty Γ A (⊃L x D E) = {!!}
   righty Γ A (∧L₁ x D) = {!!}
   righty Γ A (∧L₂ x D) = {!!}
   righty Γ A (□L x D) = {!!}
   righty Γ A (■L x D) = {!!}

   sem' : ∀{Γ A} → Γ ⇒' A → hornΓ Γ ⇒' hornC A
   sem' (init x) = {!!}
   sem' (⊃R D) = {!!}
   sem' {Γ}{A} (⊃L x D E) = ⊃L (pull x) {!!} (sem' E)
   sem' (∧R D E) = {!!}
   sem' (∧L₁ x D) = {!!}
   sem' (∧L₂ x D) = {!!}
   sem' (□R D) = {!!}
   sem' (□L x D) = {!!}
   sem' (■R D) = {!!}
   sem' (■L x D) = {!!}

{-
   sem' : ∀{Γ A} → Γ ⇒' A → hornΓ Γ ⇒' hornA A
   sem' (init x) = init (pull x)
   sem' (⊃R D) = ⊃R (sem' D)
   sem' {Γ}{A} (⊃L x D E) = ⊃L (pull x) {!!} (sem' E)
   sem' (∧R D E) = {!!}
   sem' (∧L₁ x D) = {!!}
   sem' (∧L₂ x D) = {!!}
   sem' (□R D) = {!!}
   sem' (□L x D) = {!!}
   sem' (■R D) = {!!}
   sem' (■L x D) = {!!}
-}

   foo = syn→sem {((atom "a" ⊃ atom "b") ⊃ atom "c" true)
                   :: (atom "b" true) 
                   :: []} 
                  {atom "c"} (⊃L Z (init (S Z)) (init Z)) 
   x = {!  foo !}


   mutual


      backtrack : (Γ : Ctx) (A : Type) 
         → (hornΓ Γ) ⇒' (hornA A)
         → hornΓ Γ ⇒' hornC A
      backtrack Γ (A ⊃ B) (⊃R D) = backtrack Γ B D
      backtrack Γ (A ∧ B) (∧R D E) = ∧R (backtrack Γ A D) (backtrack Γ B E)
      backtrack Γ (CORE.□ p A) (□R D) = 
         □R (wkp' (horn○₂ Γ) (backtrack (Γ ○ p) A (wkp' (horn○ Γ) D)))
      backtrack Γ (CORE.■ p A) (■R D) = 
         ■R (wkp' (horn●₂ Γ) (backtrack (Γ ● p) A (wkp' (horn●₁ Γ) D)))
   
      backtrack Γ A (init x) = {!identty !}

      backtrack Γ A (⊃L x D E) with push {Γ} x
      ... | (atom _ , () , _)
      ... | (B ⊃ C , Refl , y) = ⊃L x D (backtrack ((C true) :: Γ) A E)
      ... | (_ ∧ _ , () , _) 
      ... | (□ _ _ , () , _) 
      ... | (■ _ _ , () , _)

      backtrack Γ A (∧L₁ x D) with push {Γ} x
      ... | (atom _ , () , _)
      ... | (_ ⊃ _ , () , _)
      ... | (B ∧ C , Refl , _) = ∧L₁ x (backtrack ((B true) :: Γ) A D)
      ... | (□ _ _ , () , _) 
      ... | (■ _ _ , () , _)

      backtrack Γ A (∧L₂ x D) with push {Γ} x
      ... | (atom _ , () , _)
      ... | (_ ⊃ _ , () , _)
      ... | (B ∧ C , Refl , _) = ∧L₂ x (backtrack ((C true) :: Γ) A D)
      ... | (□ _ _ , () , _)  
      ... | (■ _ _ , () , _)

      backtrack Γ A (□L x D) with push {Γ} x
      ... | (atom _ , () , _)
      ... | (_ ⊃ _ , () , _)
      ... | (_ ∧ _ , () , _) 
      ... | (□ p B , Refl , _) = □L x (backtrack ((p said B) :: Γ) A D)
      ... | (■ _ _ , () , _)

      backtrack Γ A (■L x D) with push {Γ} x
      ... | (atom _ , () , _)
      ... | (_ ⊃ _ , () , _)
      ... | (_ ∧ _ , () , _) 
      ... | (□ _ _ , () , _) 
      ... | (■ p B , Refl , _) = ■L x (backtrack ((p implied B) :: Γ) A D)



   sem→syn : ∀{Γ A} → Γ ⇒' A → hornΓ Γ ⇒ hornA A
   sem→syn (init x) = ident (pull x)
   sem→syn (⊃R D) = ⊃R (wk' sub-wken (sem→syn D))
   sem→syn {Γ} {A} (⊃L {A'} {B} {.A} x D E) = 
     ⊃L (pull x) {! right !} (sem→syn E)
    where
      D₁ : hornΓ Γ ⇒ hornA A' 
      D₁ = sem→syn D


   sem→syn (∧R D E) = ∧R (sem→syn D) (sem→syn E)
   sem→syn (∧L₁ x D) = ∧L₁ (pull x) (sem→syn D)
   sem→syn (∧L₂ x D) = ∧L₂ (pull x) (sem→syn D)
   sem→syn (□R D) = □R (wk' {!!} (sem→syn D))
   sem→syn (□L x D) = □L (pull x) (sem→syn D)
   sem→syn {Γ} (■R D) = ■R (wk' (horn●₂ Γ) (sem→syn D))
   sem→syn (■L x D) = ■L (pull x) (sem→syn D)

