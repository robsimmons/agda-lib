open import Prelude

module Infon.Judgments where

module JUDGMENTS 
   (Type : Set)
   (Prin : Set)
   (_≡?_ : (p q : Prin) → Decidable (p ≡ q)) where

   infix 0 _true
   infix 0 _said_
   infix 0 _implied_
   data Jmt : Set where
      _true : (A : Type) → Jmt
      _said_ : (p : Prin) (A : Type) → Jmt
      _implied_ : (p : Prin) (A : Type) → Jmt
  
   Ctx = List Jmt

   open LIST.SET public hiding (refl ; sub-append-congr)
   _⊆_ : ∀{A} → List A → List A → Set
   _⊆_ = Sub

   -- Context clearing for "said"

   _○_ : Ctx → Prin → Ctx 
   [] ○ p = []
   ((A true) :: Γ) ○ p = Γ ○ p
   ((q said A) :: Γ) ○ p with p ≡? q 
   ((.p said A) :: Γ) ○ p | Inl Refl = (A true) :: (Γ ○ p)
   ... | Inr _ = Γ ○ p
   ((q implied A) :: Γ) ○ p = Γ ○ p

   pull○ : ∀{Γ p A} → (p said A) ∈ Γ → (A true) ∈ Γ ○ p
   pull○ {[]} ()
   pull○ {(A true) :: Γ} (S x) = pull○ x
   pull○ {(q said A) :: Γ} {p} x with p ≡? q
   pull○ {(p said A) :: Γ} Z | Inl Refl = Z
   pull○ {(p said A) :: Γ} (S x) | Inl Refl = S (pull○ x)
   pull○ {(p said A) :: Γ} Z | Inr contr = abort (contr Refl) 
   pull○ {(q said A) :: Γ} (S x) | Inr _ = pull○ x 
   pull○ {(q implied A) :: Γ} (S x) = pull○ x 

   congr○ : ∀{Γ p Γ'} → Γ ⊆ Γ' → (Γ ○ p) ⊆ (Γ' ○ p)
   congr○ {[]} θ ()
   congr○ {(A true) :: Γ} θ x = congr○ {Γ} (θ o sub-cons) x
   congr○ {(q said A) :: Γ} {p} θ x with p ≡? q
   congr○ {(p said A) :: Γ} θ Z | Inl Refl = pull○ (θ Z)
   congr○ {(p said A) :: Γ} θ (S x) | Inl Refl = congr○ {Γ} (θ o sub-cons) x
   congr○ {(q said A) :: Γ} θ x | Inr _ = congr○ {Γ} (θ o sub-cons) x
   congr○ {(q implied A) :: Γ} θ x = congr○ {Γ} (θ o sub-cons) x

   hmorph○ : ∀{p Γ'} (Γ : Ctx) → ((Γ ++ Γ') ○ p) ≡ ((Γ ○ p) ++ (Γ' ○ p)) 
   hmorph○ [] = refl
   hmorph○ ((A true) :: Γ) = hmorph○ Γ
   hmorph○ {p} ((q said A) :: Γ) with p ≡? q
   hmorph○ ((p said A) :: Γ) | Inl Refl = LIST.cons-cong refl (hmorph○ Γ)
   hmorph○ ((q said A) :: Γ) | Inr _ = hmorph○ Γ
   hmorph○ ((q implied A) :: Γ) = hmorph○ Γ

   eq○true : ∀{p A Γ} (Γ' : Ctx) 
      → ((Γ' ++ (A true) :: Γ) ○ p) ≡ ((Γ' ++ Γ) ○ p)
   eq○true [] = refl
   eq○true ((B true) :: Γ) = eq○true Γ
   eq○true {p} ((q said B) :: Γ) with p ≡? q
   eq○true ((p said B) :: Γ) | Inl Refl = LIST.cons-congr (eq○true Γ)
   eq○true ((q said B) :: Γ) | Inr _ = eq○true Γ
   eq○true ((q implied B) :: Γ) = eq○true Γ

   eq○implied : ∀{p q A Γ} (Γ' : Ctx) 
      → ((Γ' ++ (q implied A) :: Γ) ○ p) ≡ ((Γ' ++ Γ) ○ p)
   eq○implied [] = refl
   eq○implied ((B true) :: Γ) = eq○implied Γ
   eq○implied {p} ((q said B) :: Γ) with p ≡? q
   eq○implied ((p said B) :: Γ) | Inl Refl = LIST.cons-congr (eq○implied Γ)
   eq○implied ((q said B) :: Γ) | Inr _ = eq○implied Γ
   eq○implied ((q implied B) :: Γ) = eq○implied Γ


   -- Context clearing for "implied" and relevant properties

   _●_ : Ctx → Prin → Ctx 
   [] ● p = []
   ((A true) :: Γ) ● p = Γ ● p
   ((q said A) :: Γ) ● p with p ≡? q 
   ((.p said A) :: Γ) ● p | Inl Refl = (A true) :: (Γ ● p)
   ... | Inr _ = Γ ● p
   ((q implied A) :: Γ) ● p with p ≡? q
   ((.p implied A) :: Γ) ● p | Inl Refl = (A true) :: Γ ● p
   ... | Inr _ = Γ ● p

   pull● : ∀{Γ p A} → (p said A) ∈ Γ → (A true) ∈ Γ ● p
   pull● {[]} ()
   pull● {(A true) :: Γ} (S x) = pull● x
   pull● {(q said A) :: Γ} {p} x with p ≡? q
   pull● {(p said A) :: Γ} Z | Inl Refl = Z
   pull● {(p said A) :: Γ} (S x) | Inl Refl = S (pull● x)
   pull● {(p said A) :: Γ} Z | Inr contr = abort (contr Refl)
   pull● {(q said A) :: Γ} (S x) | Inr _ = pull● x
   pull● {(q implied A) :: Γ} {p} x with p ≡? q
   pull● {(q implied A) :: Γ} (S x) | Inl Refl = S (pull● x)
   pull● {(q implied A) :: Γ} (S x) | Inr _ = pull● x

   pull●' : ∀{Γ p A} → (p implied A) ∈ Γ → (A true) ∈ Γ ● p
   pull●' {[]} ()
   pull●' {(A true) :: Γ} (S x) = pull●' x
   pull●' {(q said A) :: Γ} {p} x with p ≡? q
   pull●' {(p said A) :: Γ} (S x) | Inl Refl = S (pull●' x)
   pull●' {(q said A) :: Γ} (S x) | Inr _ = pull●' x
   pull●' {(q implied A) :: Γ} {p} x with p ≡? q
   pull●' {(p implied A) :: Γ} Z | Inl Refl = Z
   pull●' {(p implied A) :: Γ} (S x) | Inl Refl = S (pull●' x)
   pull●' {(p implied A) :: Γ} Z | Inr contr = abort (contr Refl)
   pull●' {(q implied A) :: Γ} (S x) | Inr _ = pull●' x

   congr● : ∀{Γ p Γ'} → Γ ⊆ Γ' → (Γ ● p) ⊆ (Γ' ● p)
   congr● {[]} θ ()
   congr● {(A true) :: Γ} θ x = congr● {Γ} (θ o sub-cons) x
   congr● {(q said A) :: Γ} {p} θ x with p ≡? q
   congr● {(p said A) :: Γ} θ Z | Inl Refl = pull● (θ Z)
   congr● {(p said A) :: Γ} θ (S x) | Inl Refl = congr● {Γ} (θ o sub-cons) x
   congr● {(p said A) :: Γ} θ x | Inr _ = congr● {Γ} (θ o sub-cons) x
   congr● {(q implied A) :: Γ} {p} θ x with p ≡? q
   congr● {(p implied A) :: Γ} θ Z | Inl Refl = pull●' (θ Z)
   congr● {(p implied A) :: Γ} θ (S x) | Inl Refl = congr● {Γ} (θ o sub-cons) x
   congr● {(p implied A) :: Γ} θ x | Inr _ = congr● {Γ} (θ o sub-cons) x
   
   hmorph● : ∀{p Γ'} (Γ : Ctx) → ((Γ ++ Γ') ● p) ≡ ((Γ ● p) ++ (Γ' ● p)) 
   hmorph● [] = refl
   hmorph● ((A true) :: Γ) = hmorph● Γ
   hmorph● {p} ((q said A) :: Γ) with p ≡? q
   hmorph● ((p said A) :: Γ) | Inl Refl = LIST.cons-cong refl (hmorph● Γ)
   hmorph● ((q said A) :: Γ) | Inr _ = hmorph● Γ
   hmorph● {p} ((q implied A) :: Γ) with p ≡? q
   hmorph● ((p implied A) :: Γ) | Inl Refl = LIST.cons-cong refl (hmorph● Γ)
   hmorph● ((q implied A) :: Γ) | Inr _ = hmorph● Γ

   eq●true : ∀{p A Γ} (Γ' : Ctx) 
      → ((Γ' ++ (A true) :: Γ) ● p) ≡ ((Γ' ++ Γ) ● p)
   eq●true [] = refl
   eq●true ((B true) :: Γ) = eq●true Γ
   eq●true {p} ((q said B) :: Γ) with p ≡? q
   eq●true ((p said B) :: Γ) | Inl Refl = LIST.cons-congr (eq●true Γ)
   eq●true ((q said B) :: Γ) | Inr _ = eq●true Γ
   eq●true {p} ((q implied B) :: Γ) with p ≡? q 
   eq●true ((p implied B) :: Γ) | Inl Refl = LIST.cons-congr (eq●true Γ)
   eq●true ((q implied B) :: Γ) | Inr _ = eq●true Γ


   -- Subset relationship between the action of the judgments

   sub-○● : ∀{p} (Γ : Ctx) → (Γ ○ p) ⊆ (Γ ● p)
   sub-○● [] ()
   sub-○● ((A true) :: Γ) x = sub-○● Γ x
   sub-○● {p} ((q said A) :: Γ) x with p ≡? q
   sub-○● ((p said A) :: Γ) Z | Inl Refl = Z
   sub-○● ((p said A) :: Γ) (S x) | Inl Refl = S (sub-○● Γ x)
   sub-○● ((q said A) :: Γ) x | Inr _ = sub-○● Γ x
   sub-○● {p} ((q implied A) :: Γ) x with p ≡? q
   sub-○● ((p implied A) :: Γ) x | Inl Refl = S (sub-○● Γ x)
   sub-○● ((q implied A) :: Γ) x | Inr _ = sub-○● Γ x
