-- Natural Deduction for Full Infon Logic
-- Robert J. Simmons

{-# OPTIONS --universe-polymorphism #-}

open import Prelude hiding (⊤)
open import Infon.Core
open import Infon.NatDeduction
open import Infon.ReceivedCtx

module Infon.Received 
   (Prin : Set)
   (_≡?_ : (p q : Prin) → Decidable (p ≡ q)) where

   open CORE Prin _≡?_
   open NAT-DEDUCTION Prin _≡?_
   open RECEIVED-CTX Prin _≡?_
 
   -- Reverse-append lists, good for certain structural inductions, and other 
   -- stuff I've been needing to add to the standard library

   _>>_ : ∀{a} {A : Set a} (as bs : List A) → List A
   as >> [] = as
   as >> (x :: xs) = (x :: as) >> xs

   in-ra-l : ∀{a} {A : Set a} {x : A} {as : List A} (bs cs : List A) 
      → x ∈ (cs ++ x :: as) >> bs 
   in-ra-l [] cs = LIST.append-in cs Z
   in-ra-l (x' :: xs) cs = in-ra-l xs (x' :: cs)

   split-ra : ∀{a} {A : Set a} {a : A} (as bs : List A) 
      → a ∈ as >> bs
      → (a ∈ as) + (a ∈ bs)
   split-ra as [] n = Inl n
   split-ra as (b :: bs) n with split-ra (b :: as) bs n
   ... | Inl Z = Inr Z
   ... | Inl (S n') = Inl n'
   ... | Inr n' = Inr (S n')

   sub-rar : ∀{a} {A : Set a}
      → (xs : List A)
      → (ys : List A)
      → Sub xs (xs >> ys)
   sub-rar xs [] n = n
   sub-rar xs (x :: ys) n = sub-rar (x :: xs) ys (S n)

   sub-ral : ∀{a} {A : Set a}
      → (xs : List A)
      → (ys : List A)
      → Sub xs (ys >> xs)
   sub-ral [] ys ()
   sub-ral (x :: xs) ys Z = sub-rar (x :: ys) xs Z
   sub-ral (x :: xs) ys (S n) = sub-ral xs (x :: ys) n


   sub-append-cong : ∀{a} {A : Set a} {xs2 ys2 : List A}
      (xs1 ys1 : List A)
      → Sub xs1 ys1
      → Sub xs2 ys2
      → Sub (xs1 ++ xs2) (ys1 ++ ys2)
   sub-append-cong [] [] f g n = g n
   sub-append-cong [] (_ :: ys1) f g n = S (sub-append-cong [] ys1 (λ ()) g n)
   sub-append-cong (x :: xs1) ys1 f g Z = sub-appendr ys1 _ (f Z)
   sub-append-cong (x :: xs1) ys1 f g (S n) = 
     sub-append-cong xs1 ys1 (f o S) g n

   sub-append-congl : ∀{a} {A : Set a} {xs2 : List A}
      (xs1 ys1 : List A)
      → Sub xs1 ys1
      → Sub (xs1 ++ xs2) (ys1 ++ xs2)
   sub-append-congl xs1 ys1 f = sub-append-cong xs1 ys1 f (sub-eq refl)

   sub-append-congr : ∀{a} {A : Set a} {xs2 ys2 : List A}
      (xs1 : List A)
      → Sub xs2 ys2
      → Sub (xs1 ++ xs2) (xs1 ++ ys2)
   sub-append-congr xs1 f = sub-append-cong xs1 xs1 (sub-eq refl) f


   -- Given the context clearing operations, the encoding is straightforward

   infix 1 _⊢'_
   data _⊢'_ (Δ : Ctx') : Type → Set where
      hyp : ∀{A} 
         → (x : A ∈ Δ) 
         → Δ ⊢' A
      ⊤I : Δ ⊢' ⊤
      ⊃I : ∀{A B}
         → (D : A :: Δ ⊢' B)
         → Δ ⊢' A ⊃ B
      ⊃E : ∀{A B} 
         → (D : Δ ⊢' A ⊃ B)
         → (E : Δ ⊢' A) 
         → Δ ⊢' B
      ∧I : ∀{A B}
         → (D : Δ ⊢' A)
         → (E : Δ ⊢' B)
         → Δ ⊢' A ∧ B
      ∧E₁ : ∀{A B}
         → (D : Δ ⊢' A ∧ B)
         → Δ ⊢' A
      ∧E₂ : ∀{A B}
         → (D : Δ ⊢' A ∧ B)
         → Δ ⊢' B
      □I : ∀{A p} 
         → (D : Δ ○' p ⊢' A)
         → Δ ⊢' □ p A
      ■I : ∀{A p} 
         → (D : Δ ●' p ⊢' A)
         → Δ ⊢' ■ p A

   wk' : ∀{Δ Δ' A} → Δ ⊆ Δ' → Δ ⊢' A → Δ' ⊢' A
   wk' θ (hyp x) = hyp (θ x)
   wk' θ ⊤I = ⊤I
   wk' θ (⊃I D) = ⊃I (wk' (sub-cons-congr θ) D)
   wk' θ (⊃E D E) = ⊃E (wk' θ D) (wk' θ E)
   wk' θ (∧I D E) = ∧I (wk' θ D) (wk' θ E)
   wk' θ (∧E₁ D) = ∧E₁ (wk' θ D)
   wk' θ (∧E₂ D) = ∧E₂ (wk' θ D)
   wk' θ (□I D) = □I (wk' (congrR○ θ) D)
   wk' θ (■I D) = ■I (wk' (congrR● θ) D)



   -- Equivalence is established relative to a context-equivalence operation.

   -- The simple direction is showing that provability in the judgmental system
   -- implies provability in the received system. We use the same bogus trick
   -- for encoding modal elimination that the original paper uses: we introduce
   -- an un-reducable beta redex. 

   -- Beyond this, the only necessary lemma is showing that context clearing 
   -- commutes with the erasure operation.

   ○⁻ : ∀{p} → (Γ : Ctx) → ((Γ ○ p) ⁻) ⊆ ((Γ ⁻) ○' p)
   ○⁻ [] = sub-eq refl
   ○⁻ (((atom Q) true) :: Γ) = ○⁻ Γ
   ○⁻ ((⊤ true) :: Γ) = ○⁻ Γ
   ○⁻ (((A ⊃ B) true) :: Γ) = ○⁻ Γ
   ○⁻ (((A ∧ B) true) :: Γ) = ○⁻ Γ
   ○⁻ {p} (((□ q A) true) :: Γ) with p ≡? q 
   ○⁻ {.p} (((□ p A) true) :: Γ) | Inl Refl = S o ○⁻ Γ
   ... | Inr _ = ○⁻ Γ
   ○⁻ (((■ q A) true) :: Γ) = ○⁻ Γ
   ○⁻ {p} ((q said A) :: Γ) with p ≡? q
   ○⁻ {.p} ((p said A) :: Γ) | Inl Refl = sub-cons-congr (○⁻ Γ)
   ... | Inr _ = ○⁻ Γ
   ○⁻ ((q implied A) :: Γ) = ○⁻ Γ

   ●⁻ : ∀{p} → (Γ : Ctx) → ((Γ ● p) ⁻) ⊆ ((Γ ⁻) ●' p)
   ●⁻ [] = sub-eq refl
   ●⁻ (((atom Q) true) :: Γ) = ●⁻ Γ
   ●⁻ ((⊤ true) :: Γ) = ●⁻ Γ
   ●⁻ (((A ⊃ B) true) :: Γ) = ●⁻ Γ
   ●⁻ (((A ∧ B) true) :: Γ) = ●⁻ Γ
   ●⁻ {p} (((□ q A) true) :: Γ) with p ≡? q 
   ●⁻ {.p} (((□ p A) true) :: Γ) | Inl Refl = S o ●⁻ Γ
   ... | Inr _ = ●⁻ Γ
   ●⁻ {p} (((■ q A) true) :: Γ) with p ≡? q
   ●⁻ {.p} (((■ p A) true) :: Γ) | Inl Refl = S o ●⁻ Γ
   ... | Inr _ = ●⁻ Γ
   ●⁻ {p} ((q said A) :: Γ) with p ≡? q
   ●⁻ {.p} ((p said A) :: Γ) | Inl Refl = sub-cons-congr (●⁻ Γ)
   ... | Inr _ = ●⁻ Γ
   ●⁻ {p} ((q implied A) :: Γ) with p ≡? q
   ●⁻ {.p} ((p implied A) :: Γ) | Inl Refl = sub-cons-congr (●⁻ Γ)
   ... | Inr _ = ●⁻ Γ

   recon→orig : ∀{Γ A} → Γ ⊢ A → Γ ⁻ ⊢' A
   recon→orig (hyp x) = hyp (pull x)
   recon→orig ⊤I = ⊤I
   recon→orig (⊃I D) = ⊃I (recon→orig D)
   recon→orig (⊃E D E) = ⊃E (recon→orig D) (recon→orig E)
   recon→orig (∧I D E) = ∧I (recon→orig D) (recon→orig E)
   recon→orig (∧E₁ D) = ∧E₁ (recon→orig D)
   recon→orig (∧E₂ D) = ∧E₂ (recon→orig D)
   recon→orig {Γ} (□I D) = □I (wk' (○⁻ Γ) (recon→orig D))
   recon→orig (□E D E) = ⊃E (⊃I (recon→orig E)) (recon→orig D)
   recon→orig {Γ} (■I D) = ■I (wk' (●⁻ Γ) (recon→orig D))
   recon→orig (■E D E) = ⊃E (⊃I (recon→orig E)) (recon→orig D)

   -- It is more complex to show that provability in the received system
   -- implies provability in the original system. The critical move is that,
   -- when we are on the cusp of translating an introduction rule, we need
   -- to perform enough eliminations "at the last minute" in order to save
   -- every relevant fact in the context. 

   -- This is the proof that we can perform all the eliminations we need
   -- to perform. The "big idea" is clear enough, but it took some time
   -- to fiddle with everything until everything lined up appropriately, and
   -- the resulting theorem statement isn't exactly intuitive.

   sub-fact : ∀{Γ} {J : Jmt} → ([ J ] >> Γ) ⊆ (J :: ([] >> Γ))
   sub-fact {Γ} x with split-ra [ _ ] Γ x
   ... | Inl Z = Z
   ... | Inl (S ())
   ... | Inr n' = S (sub-ral Γ [] n')

   left○ : ∀{Γ Γ' Γ'' p A} 
      → (Γ ○⁺ p >> Γ'') ++ (Γ >> Γ') ⊢ A 
      → ([] >> Γ'') ++ (Γ >> Γ') ⊢ A
   left○ {[]} D = D
   left○ {(atom Q true) :: Γ} {Γ'} {Γ''} D = 
      left○ {Γ} {(atom Q true) :: Γ'} {Γ''} D
   left○ {(⊤ true) :: Γ} {Γ'} {Γ''} D = 
      left○ {Γ} {(⊤ true) :: Γ'} {Γ''} D
   left○ {(A ⊃ B true) :: Γ} {Γ'} {Γ''} D = 
      left○ {Γ} {(A ⊃ B true) :: Γ'} {Γ''} D
   left○ {(A ∧ B true) :: Γ} {Γ'} {Γ''}  D = 
      left○ {Γ} {(A ∧ B true) :: Γ'} {Γ''} D
   left○ {(□ q A true) :: Γ} {Γ'} {Γ''} {p} D with p ≡? q
   left○ {(□ .p A true) :: Γ} {Γ'} {Γ''} {p} {C} D | Inl Refl = □E D₁ D₃
    where
      D₁ : [] >> Γ'' ++ ((□ p A true) :: Γ) >> Γ' ⊢ □ p A
      D₁ = hyp (LIST.append-in ([] >> Γ'') (in-ra-l Γ' []))

      D₂ : [ p said A ] >> Γ'' ++ ((□ p A true) :: Γ) >> Γ' ⊢ C
      D₂ = left○ {Γ} {(□ p A true) :: Γ'} {(p said A) :: Γ''} D

      D₃ : ((p said A) :: [] >> Γ'') ++ ((□ p A true) :: Γ) >> Γ' ⊢ C
      D₃ = wk (sub-append-congl _ _ (sub-fact {Γ''})) D₂

   left○ {(□ q A true) :: Γ} {Γ'} {Γ''} D | Inr _ = 
      left○ {Γ} {(□ q A true) :: Γ'} {Γ''} D
   left○ {(■ q A true) :: Γ} {Γ'} {Γ''} D = 
      left○ {Γ} {(■ q A true) :: Γ'} {Γ''} D
   left○ {(q said A) :: Γ} {Γ'} {Γ''} D = 
      left○ {Γ} {(q said A) :: Γ'} {Γ''} D
   left○ {(q implied A) :: Γ} {Γ'} {Γ''} D = 
      left○ {Γ} {(q implied A) :: Γ'} {Γ''} D

   left● : ∀{Γ Γ' Γ'' p A} 
      → (Γ ●⁺ p >> Γ'') ++ (Γ >> Γ') ⊢ A 
      → ([] >> Γ'') ++ (Γ >> Γ') ⊢ A
   left● {[]} D = D
   left● {(atom Q true) :: Γ} {Γ'} {Γ''} D = 
      left● {Γ} {(atom Q true) :: Γ'} {Γ''} D
   left● {(⊤ true) :: Γ} {Γ'} {Γ''} D = 
      left● {Γ} {(⊤ true) :: Γ'} {Γ''} D
   left● {(A ⊃ B true) :: Γ} {Γ'} {Γ''} D = 
      left● {Γ} {(A ⊃ B true) :: Γ'} {Γ''} D
   left● {(A ∧ B true) :: Γ} {Γ'} {Γ''}  D = 
      left● {Γ} {(A ∧ B true) :: Γ'} {Γ''} D
   left● {(□ q A true) :: Γ} {Γ'} {Γ''} {p} D with p ≡? q
   left● {(□ .p A true) :: Γ} {Γ'} {Γ''} {p} {C} D | Inl Refl = □E D₁ D₃
    where
      D₁ : [] >> Γ'' ++ ((□ p A true) :: Γ) >> Γ' ⊢ □ p A
      D₁ = hyp (LIST.append-in ([] >> Γ'') (in-ra-l Γ' []))

      D₂ : [ p said A ] >> Γ'' ++ ((□ p A true) :: Γ) >> Γ' ⊢ C
      D₂ = left● {Γ} {(□ p A true) :: Γ'} {(p said A) :: Γ''} D

      D₃ : ((p said A) :: [] >> Γ'') ++ ((□ p A true) :: Γ) >> Γ' ⊢ C
      D₃ = wk (sub-append-congl _ _ (sub-fact {Γ''})) D₂

   left● {(□ q A true) :: Γ} {Γ'} {Γ''} D | Inr _ = 
      left● {Γ} {(□ q A true) :: Γ'} {Γ''} D
   left● {(■ q A true) :: Γ} {Γ'} {Γ''} {p} D with p ≡? q
   left● {(■ .p A true) :: Γ} {Γ'} {Γ''} {p} {C} D | Inl Refl = ■E D₁ D₃
    where
      D₁ : [] >> Γ'' ++ ((■ p A true) :: Γ) >> Γ' ⊢ ■ p A
      D₁ = hyp (LIST.append-in ([] >> Γ'') (in-ra-l Γ' []))
  
      D₂ : [ p implied A ] >> Γ'' ++ ((■ p A true) :: Γ) >> Γ' ⊢ C
      D₂ = left● {Γ} {(■ p A true) :: Γ'} {(p implied A) :: Γ''} D

      D₃ : ((p implied A) :: [] >> Γ'') ++ ((■ p A true) :: Γ) >> Γ' ⊢ C
      D₃ = wk (sub-append-congl _ _ (sub-fact {Γ''})) D₂

   left● {(■ q A true) :: Γ} {Γ'} {Γ''} D | Inr _ = 
      left● {Γ} {(■ q A true) :: Γ'} {Γ''} D
   left● {(q said A) :: Γ} {Γ'} {Γ''} D = 
      left● {Γ} {(q said A) :: Γ'} {Γ''} D
   left● {(q implied A) :: Γ} {Γ'} {Γ''} D = 
      left● {Γ} {(q implied A) :: Γ'} {Γ''} D

   -- The proof has two interesting parts. First, when we reach a hypothesis we
   -- may have to do a localized large elimination, and when we reach an 
   -- introduction rule we have to do the "last minute" application of all the 
   -- potentially relevant elimination rules.

   orig→recon : ∀{Γ Δ A} → Δ ⊆ Γ ⁻ → Δ ⊢' A → Γ ⊢ A
   orig→recon {Γ} θ (hyp x) with pull⁻ {Γ} (θ x)
   ... | Inl x' = hyp x'
   ... | Inr (Inl (p , A , Refl , x')) = □I (hyp (pull○ x'))
   ... | Inr (Inr (p , A , Refl , x')) = ■I (hyp (pull●' x'))
   orig→recon θ ⊤I = ⊤I
   orig→recon θ (⊃I D) = ⊃I (orig→recon (sub-cons-congr θ) D)
   orig→recon θ (⊃E D E) = ⊃E (orig→recon θ D) (orig→recon θ E)
   orig→recon θ (∧I D E) = ∧I (orig→recon θ D) (orig→recon θ E)
   orig→recon θ (∧E₁ D) = ∧E₁ (orig→recon θ D)
   orig→recon θ (∧E₂ D) = ∧E₂ (orig→recon θ D)
   orig→recon {Γ} {Δ} {□ p A} θ (□I D) = D₂
    where
      D₁ : Γ ○⁺ p ++ Γ ⊢ □ p A
      D₁ = □I (orig→recon (sub○⁺ {Γ} Δ θ) D)
  
      D₂ : Γ ⊢ □ p A 
      D₂ = left○ {Γ} {[]} {[]} D₁  

   orig→recon {Γ} {Δ} {■ p A} θ (■I D) = D₂
    where
      D₁ : Γ ●⁺ p ++ Γ ⊢ ■ p A
      D₁ = ■I (orig→recon (sub●⁺ {Γ} Δ θ) D)

      D₂ : Γ ⊢ ■ p A
      D₂ = left● {Γ} {[]} {[]} D₁

