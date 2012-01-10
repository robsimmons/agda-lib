{-- The identity expansion theorem holds for an obvious reason that is 
nevertheless too subtle for Agda's termination checker: expand⁺ calls to 
expand⁻ on negative types (without getting smaller) and expand⁻ calls to
expand⁺ on positive types (without getting smaller). 

It's a simple (but non-structural) termination argument that makes it work. At 
the price of making the theormen uglier, we could make everything check by loop
unrolling --}

{-# OPTIONS --no-termination-check #-}

open import Prelude hiding (⊥; ⊤)
open import BabyFoc.Foc

module BabyFoc.Eta where

open LIST.SET

-- Focal substitution

-- Values for value variables

fsubV⁺ : ∀{א Γ A B} (Γ' : Ctx)
  → Value א Γ A
  → Value (A :: א) (Γ' ++ Γ) B
  → Value א (Γ' ++ Γ) B 

fsubN⁺ : ∀{א Γ A U} (Γ' : Ctx)
  → Value א Γ A
  → Term (A :: א) (Γ' ++ Γ) U
  → Term א (Γ' ++ Γ) U

fsubSp⁺ : ∀{א Γ A B U} (Γ' : Ctx)
  → Value א Γ A
  → Spine (A :: א) (Γ' ++ Γ) B U
  → Spine א (Γ' ++ Γ) B U

fsubV⁺ Γ' V (hyp⁺ Z) = wkV (sub-appendl _ Γ') V
fsubV⁺ Γ' V (hyp⁺ (S n)) = hyp⁺ n
fsubV⁺ Γ' V (pR x) = pR x
fsubV⁺ Γ' V (↓R pf N) = ↓R pf (fsubN⁺ Γ' V N)
fsubV⁺ Γ' V (∨R₁ V') = ∨R₁ (fsubV⁺ Γ' V V')
fsubV⁺ Γ' V (∨R₂ V') = ∨R₂ (fsubV⁺ Γ' V V')
fsubV⁺ Γ' V ⊤R = ⊤R

fsubN⁺ Γ' V (foc pf₁ x pf₂ Sp) = foc pf₁ x pf₂ (fsubSp⁺ Γ' V Sp)
fsubN⁺ Γ' V (⊥L x) = ⊥L x
fsubN⁺ Γ' V (∨L x N₁ N₂) = 
  ∨L x (fsubN⁺ (_ :: Γ') V N₁) (fsubN⁺ (_ :: Γ') V N₂)
fsubN⁺ Γ' V (⊤L x N) = ⊤L x (fsubN⁺ Γ' V N)
fsubN⁺ Γ' V (rfoc pf V') = rfoc pf (fsubV⁺ Γ' V V')
fsubN⁺ Γ' V (⊃R N) = ⊃R (fsubN⁺ (_ :: Γ') V N)

fsubSp⁺ Γ' V hyp⁻ = hyp⁻
fsubSp⁺ Γ' V pL = pL
fsubSp⁺ Γ' V (↑L pf N) = ↑L pf (fsubN⁺ (_ :: Γ') V N)
fsubSp⁺ Γ' V (⊃L V' Sp) = ⊃L (fsubV⁺ Γ' V V') (fsubSp⁺ Γ' V Sp)

fsub⁺ : ∀{א Γ A U} → Value א Γ A → Term (A :: א) Γ U → Term א Γ U
fsub⁺ = fsubN⁺ []

-- Spines for spine variables

fsubN⁻ : ∀{א Γ A U} (Γ' : List Type) 
  → U stable
  → Spine א Γ A U
  → Term א (Γ' ++ Γ) (Abs A) 
  → Term א (Γ' ++ Γ) U 

fsubSp⁻ : ∀{א Γ A U B} (Γ' : List Type) 
  → U stable
  → Spine א Γ A U
  → Spine א (Γ' ++ Γ) B (Abs A)
  → Spine א (Γ' ++ Γ) B U 

fsubN⁻ Γ' pf Sp (foc pf₁ x pf₂ Sp') = foc pf x pf₂ (fsubSp⁻ Γ' pf Sp Sp')
fsubN⁻ Γ' pf Sp (⊥L x) = ⊥L x
fsubN⁻ Γ' pf Sp (∨L x N₁ N₂) = 
  ∨L x (fsubN⁻ (_ :: Γ') pf Sp N₁) (fsubN⁻ (_ :: Γ') pf Sp N₂)
fsubN⁻ Γ' pf Sp (⊤L x N) = ⊤L x (fsubN⁻ Γ' pf Sp N)

fsubSp⁻ Γ' pf Sp hyp⁻ = wkSp (sub-appendl _ Γ') Sp
fsubSp⁻ Γ' pf Sp (↑L pf' N) = ↑L pf' (fsubN⁻ (_ :: Γ') pf Sp N)
fsubSp⁻ Γ' pf Sp (⊃L V Sp') = ⊃L V (fsubSp⁻ Γ' pf Sp Sp')

fsub⁻ : ∀{א Γ A U} → U stable → Spine א Γ A U → Term א Γ (Abs A) → Term א Γ U 
fsub⁻ = fsubN⁻ []


-- Identity expansion

expand⁺ : ∀{A א Γ U} → Term (A :: א) Γ U → Term א (A :: Γ) U
expand⁻ : ∀{A א Γ} → Term א Γ (Abs A) → Term א Γ (Reg A)

expand⁺ {a Q ⁺} N = fsub⁺ (pR Z) (wkN sub-wken N)
expand⁺ {⊥} N = ⊥L Z
expand⁺ {A ∨ B} N = 
  ∨L Z (expand⁺ (fsub⁺ (∨R₁ (hyp⁺ Z)) (wkN' sub-wkex sub-wken N)))
    (expand⁺ (fsub⁺ (∨R₂ (hyp⁺ Z)) (wkN' sub-wkex sub-wken N)))
expand⁺ {⊤} N = ⊤L Z (fsub⁺ ⊤R (wkN sub-wken N))
--
expand⁺ {a Q ⁻} N = fsub⁺ (↓R <> (expand⁻ (foc <> Z <> hyp⁻))) (wkN sub-wken N)
expand⁺ {A ⊃ B} N = fsub⁺ (↓R <> (expand⁻ (foc <> Z <> hyp⁻))) (wkN sub-wken N)

expand⁻ {a Q ⁻} N = fsub⁻ <> pL N
expand⁻ {A ⊃ B} N = 
  ⊃R (expand⁺ {A} 
       (expand⁻ {B} 
         (fsub⁻ <> (⊃L (hyp⁺ Z) hyp⁻) 
           (wkN' sub-wken (λ x → x) N)))) 
--
expand⁻ {a Q ⁺} N = fsub⁻ <> (↑L <> (expand⁺ (rfoc <> (hyp⁺ Z)))) N
expand⁻ {⊥} N = fsub⁻ <> (↑L <> (expand⁺ (rfoc <> (hyp⁺ Z)))) N
expand⁻ {A ∨ B} N = fsub⁻ <> (↑L <> (expand⁺ (rfoc <> (hyp⁺ Z)))) N
expand⁻ {⊤} N = fsub⁻ <> (↑L <> (expand⁺ (rfoc <> (hyp⁺ Z)))) N


-- Identity property

identity : ∀{A Γ} → A ∈ Γ → Term [] Γ (Reg A)

identity {a Q ⁺} x = wkN (sub-cntr x) (expand⁺ (rfoc <> (hyp⁺ Z)))
identity {⊥} x = wkN (sub-cntr x) (expand⁺ (rfoc <> (hyp⁺ Z)))
identity {A ∨ B} x = wkN (sub-cntr x) (expand⁺ (rfoc <> (hyp⁺ Z)))
identity {⊤} x = wkN (sub-cntr x) (expand⁺ (rfoc <> (hyp⁺ Z)))
--
identity {a Q ⁻} x = expand⁻ (foc <> x <> hyp⁻)
identity {A ⊃ B} x = expand⁻ (foc <> x <> hyp⁻)

