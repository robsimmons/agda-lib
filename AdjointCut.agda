open import Prelude hiding (Level)
import Adjoint

module AdjointCut 
  (Level : Set)
  (True : Level)
  (_≤_ : Level → Level → Set)
  (refl≤ : (L : Level) → L ≤ L)
  (trans≤ : ∀{L1 L2 L3} → L1 ≤ L2 → L2 ≤ L3 → L1 ≤ L3)
  (truth : (L : Level) → True ≤ L)
  (dec≤ : (L1 L2 : Level) → Decidable (L1 ≤ L2)) where

open Adjoint Level True _≤_ refl≤ trans≤ truth dec≤

fromctx : ∀{A B Γ} (Γ' : Ctx) → B ∈ (Γ' ++ A :: Γ) → (A ≡ B) + (B ∈ (Γ' ++ Γ))
fromctx [] Z = Inl Refl
fromctx [] (S x) = Inr x
fromctx (A :: Γ') Z = Inr Z
fromctx (A :: Γ') (S x) with fromctx Γ' x
... | Inl Refl = Inl Refl
... | Inr x' = Inr (S x')

-- Substitution

subst⁺ : ∀{Γ A L C}
  → Value [] (clear Γ L) (A , L)
  → Case [] Γ (A , L) (Reg C)
  → Term [] Γ (Reg C)

subst⁻ : ∀{Γ A C}
  → Reg C stable⁻
  → Term [] Γ (Reg A)
  → Spine [] Γ A (Reg C)
  → Term [] Γ (Reg C)

{-

substV : ∀{Γ A H} (Γ' : Ctx)
  → Term [] (Γ' ++ Γ) (Reg A)
  → Value [] (Γ' ++ (↓ A) :: Γ) H
  → Value [] (Γ' ++ Γ) H
-}

rsubstV : ∀{Γ A C L L'} (Γ' : Ctx)
  → Term [] (clear (Γ' ++ Γ) L) (Reg A)
  → Value [] (Γ' ++ (↓ A , L) :: Γ) (C , L')
  → Value [] (Γ' ++ Γ) (C , L')

rsubstN : ∀{Γ A C L} (Γ' : Ctx)
  → Term [] (clear (Γ' ++ Γ) L) (Reg A)
  → Term [] (Γ' ++ (↓ A , L) :: Γ) (Reg C)
  → Term [] (Γ' ++ Γ) (Reg C)

rsubstNI : ∀{Γ A C L Ω} (Γ' : Ctx)
  → Term [] (clear (Γ' ++ Γ) L) (Reg A)
  → Case [] (Γ' ++ (↓ A , L) :: Γ) Ω (Reg C)
  → Case [] (Γ' ++ Γ) Ω (Reg C)

rsubstSp : ∀{Γ A C L B} (Γ' : Ctx)
  → Term []  (clear (Γ' ++ Γ) L) (Reg A)
  → Spine [] (Γ' ++ (↓ A , L) :: Γ) B (Reg C)
  → Spine [] (Γ' ++ Γ) B (Reg C)

{-
substNI : ∀{Γ A H C} (Γ' : Ctx)
  → Term [] (Γ' ++ Γ) (Reg A)
  → Case [] (Γ' ++ (↓ A) :: Γ) H (Reg C)
  → Case [] (Γ' ++ Γ) H (Reg C)

substSp : ∀{Γ A B C} (Γ' : Ctx)
  → Term [] (Γ
-}

lsubstN : ∀{Γ C A} (Γ' : Ctx)
  → Reg C stable⁻
  → Term [] (Γ' ++ Γ) (Reg (↑ A))
  → Case [] (Γ' ++ Γ) (A , True) (Reg C)
  → Term [] (Γ' ++ Γ) (Reg C)

lsubstNI : ∀{Γ C Ω A} (Γ' : Ctx)
  → Reg C stable⁻
  → Case [] (Γ' ++ Γ) Ω (Reg (↑ A))
  → Case [] (Γ' ++ Γ) (A , True) (Reg C)
  → Case [] (Γ' ++ Γ) Ω (Reg C)

lsubstSp : ∀{Γ C B A} (Γ' : Ctx)
  → Reg C stable⁻
  → Spine [] (Γ' ++ Γ) B (Reg (↑ A))
  → Case [] (Γ' ++ Γ) (A , True) (Reg C)
  → Spine [] (Γ' ++ Γ) B (Reg C)

subst⁺ (hyp⁺ ()) N
subst⁺ (pR x) (L pf⁺ N) = wk (LIST.SET.sub-cntr (snd (inclear-necc x))) N
subst⁺ (↓R N) (L pf⁺ N') = rsubstN [] N N'
subst⁺ {Γ} (!R pf≤ V) (!L NI) = subst⁺ (wk (clearer' {Γ} pf≤) V) (NI pf≤)
subst⁺ (!R pf≤ V) (L () N)

subst⁻ pf (↓L pf⁻ x Sp) pL = ↓L pf⁻ x Sp
subst⁻ pf (↓L pf⁻ x Sp) (↑L NI) = ↓L {!pf!} x (lsubstSp [] {!pf!} Sp NI)
subst⁻ pf (↓L () x Sp) (⊃L V Sp')
subst⁻ pf (↓L () x Sp) (∧⁻L₁ Sp')
subst⁻ pf (↓L () x Sp) (∧⁻L₂ Sp')
subst⁻ pf (↑R V) (↑L NI) = subst⁺ (wk (LIST.SET.sub-eq cleartrue) V) NI
subst⁻ pf (⊃R NI) (⊃L V Sp) = 
  subst⁻ {!pf!} (subst⁺ (wk (LIST.SET.sub-eq cleartrue) V) NI) Sp
subst⁻ pf ⊤⁻R ()
subst⁻ pf (∧⁻R N₁ N₂) (∧⁻L₁ N') = subst⁻ {!pf!} N₁ N'
subst⁻ pf (∧⁻R N₁ N₂) (∧⁻L₂ N') = subst⁻ {!pf!} N₂ N'

rsubstV Γ' N (hyp⁺ ())
rsubstV Γ' N (pR x) with fromctx Γ' x
... | Inl ()
... | Inr y = pR y
rsubstV Γ' N (↓R N') = ↓R (rsubstN Γ' N N')
rsubstV Γ' N (!R pf≤ V) = !R pf≤ {!V!}
 -- This one is actually difficult to get past the termination checker, but it
 -- is certainly true: Either the !R didn't get rid of the formula, and we 
 -- continue with the subst or else the !R did get rid of the formula, and we
 -- can just stop

rsubstN Γ' N (↓L pf⁻ x Sp) with fromctx Γ' x
... | Inl Refl = subst⁻ {!pf⁻!} (wk (snd o inclear-necc) N) (rsubstSp Γ' N Sp)
... | Inr y = ↓L {!pf⁻!} y (rsubstSp Γ' N Sp)
rsubstN Γ' N (↑R V) = ↑R (rsubstV Γ' N V)
rsubstN Γ' N (⊃R NI) = ⊃R (rsubstNI Γ' N NI)
rsubstN Γ' N ⊤⁻R = ⊤⁻R
rsubstN Γ' N (∧⁻R N₁ N₂) = ∧⁻R (rsubstN Γ' N N₁) (rsubstN Γ' N N₂)

rsubstNI {Γ} {A} {C} {L = L1} {Ω = (B , L2)} Γ' N (L pf⁺ N') = 
  L pf⁺ (rsubstN (_ :: Γ') Nwk N')
 where
  Nwk : Term [] (clear ((B , L2) :: Γ' ++ Γ) L1) (Reg A)
  Nwk with dec≤ L1 L2
  ... | Inl _ = wk LIST.SET.sub-wken N
  ... | Inr _ = N
rsubstNI Γ' N (!L NI) = !L (λ pf → rsubstNI Γ' N (NI pf))

rsubstSp Γ' N pL = pL
rsubstSp Γ' N (↑L NI) = ↑L (rsubstNI Γ' N NI)
rsubstSp Γ' N (⊃L V Sp) = ⊃L (rsubstV Γ' N V) (rsubstSp Γ' N Sp)
rsubstSp Γ' N (∧⁻L₁ Sp) = ∧⁻L₁ (rsubstSp Γ' N Sp)
rsubstSp Γ' N (∧⁻L₂ Sp) = ∧⁻L₂ (rsubstSp Γ' N Sp)

lsubstN Γ' pf (↓L pf⁻ x Sp) NI = ↓L {!pf!} x (lsubstSp Γ' {!pf!} Sp NI)
lsubstN Γ' pf (↑R V) NI = subst⁺ (wk (LIST.SET.sub-eq cleartrue) V) NI

lsubstNI Γ' pf (L pf⁺ N) NI = 
  L pf⁺ (lsubstN (_ :: Γ') {!pf!} N (wk LIST.SET.sub-wken NI))
lsubstNI Γ' pf (!L NI') NI = !L (λ pf' → lsubstNI Γ' {!pf!} (NI' pf') NI)

lsubstSp Γ' pf (↑L NI') NI = ↑L (lsubstNI Γ' {!pf!} NI' NI)
lsubstSp Γ' pf (⊃L V Sp) NI = ⊃L V (lsubstSp Γ' {!pf!} Sp NI)
lsubstSp Γ' pf (∧⁻L₁ Sp) NI = ∧⁻L₁ (lsubstSp Γ' {!pf!} Sp NI)
lsubstSp Γ' pf (∧⁻L₂ Sp) NI = ∧⁻L₂ (lsubstSp Γ' {!pf!} Sp NI)
