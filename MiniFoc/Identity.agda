open import Prelude hiding (⊥; ⊤)
open import MiniFoc.Foc

module MiniFoc.Identity where

open LIST.SET

-- Focal substitution

-- Values for value variables

fsub⁺ : ∀{א Γ A Form} (Γ' : Ctx)
  → Value א Γ A
  → Exp (A :: א) (Γ' ++ Γ) Form
  → Exp א (Γ' ++ Γ) Form

fsub⁺ Γ' V (hyp⁺ Z) = wk (sub-appendl _ Γ') V
fsub⁺ Γ' V (hyp⁺ (S n)) = hyp⁺ n
fsub⁺ Γ' V (pR x) = pR x
fsub⁺ Γ' V (↓R N) = ↓R (fsub⁺ Γ' V N)
fsub⁺ Γ' V (∨R₁ V') = ∨R₁ (fsub⁺ Γ' V V')
fsub⁺ Γ' V (∨R₂ V') = ∨R₂ (fsub⁺ Γ' V V')
fsub⁺ Γ' V ⊤R = ⊤R

fsub⁺ Γ' V (↓L pf₁ x Sp) = ↓L pf₁ x (fsub⁺ Γ' V Sp)
fsub⁺ Γ' V (⊥L x) = ⊥L x
fsub⁺ Γ' V (∨L x N₁ N₂) = 
  ∨L x (fsub⁺ (_ :: Γ') V N₁) (fsub⁺ (_ :: Γ') V N₂)
fsub⁺ Γ' V (⊤L x N) = ⊤L x (fsub⁺ Γ' V N)
fsub⁺ Γ' V (↑R V') = ↑R (fsub⁺ Γ' V V')
fsub⁺ Γ' V (⊃R N) = ⊃R (fsub⁺ (_ :: Γ') V N)

fsub⁺ Γ' V hyp⁻ = hyp⁻
fsub⁺ Γ' V pL = pL
fsub⁺ Γ' V (↑L N) = ↑L (fsub⁺ (_ :: Γ') V N)
fsub⁺ Γ' V (⊃L V' Sp) = ⊃L (fsub⁺ Γ' V V') (fsub⁺ Γ' V Sp)


-- Spines for spine variables

fsub⁻ : ∀{א Γ A U} (Γ' : Ctx) 
  → U stable
  → Spine א Γ A U
  → Term א (Γ' ++ Γ) (Abs A) 
  → Term א (Γ' ++ Γ) U 

fsubSp⁻ : ∀{א Γ A U B} (Γ' : Ctx) 
  → U stable
  → Spine א Γ A U
  → Spine א (Γ' ++ Γ) B (Abs A)
  → Spine א (Γ' ++ Γ) B U 

fsub⁻ Γ' pf Sp (↓L pf₁ x Sp') = ↓L pf x (fsubSp⁻ Γ' pf Sp Sp')
fsub⁻ Γ' pf Sp (⊥L x) = ⊥L x
fsub⁻ Γ' pf Sp (∨L x N₁ N₂) = 
  ∨L x (fsub⁻ (_ :: Γ') pf Sp N₁) (fsub⁻ (_ :: Γ') pf Sp N₂)
fsub⁻ Γ' pf Sp (⊤L x N) = ⊤L x (fsub⁻ Γ' pf Sp N)

fsubSp⁻ Γ' pf Sp hyp⁻ = wk (sub-appendl _ Γ') Sp
fsubSp⁻ Γ' pf Sp (↑L N) = ↑L (fsub⁻ (_ :: Γ') pf Sp N)
fsubSp⁻ Γ' pf Sp (⊃L V Sp') = ⊃L V (fsubSp⁻ Γ' pf Sp Sp')


-- Identity expansion

expand⁺ : ∀{A א Γ U} → Term (A :: א) Γ U → Term א (A :: Γ) U
expand⁻ : ∀{A א Γ} → Term א Γ (Abs A) → Term א Γ (Reg A)

expand⁺ {a Q .⁺} N = fsub⁺ [] (pR Z) (wk sub-wken N) 
expand⁺ {↓ A} N = fsub⁺ [] (↓R (expand⁻ (↓L <> Z hyp⁻))) (wk sub-wken N)
expand⁺ {⊥} N = ⊥L Z
expand⁺ {A ∨ B} N = 
  ∨L Z (expand⁺ (fsub⁺ [] (∨R₁ (hyp⁺ Z)) (wk' sub-wkex sub-wken N))) 
    (expand⁺ (fsub⁺ [] (∨R₂ (hyp⁺ Z)) (wk' sub-wkex sub-wken N)))
expand⁺ {⊤} N = ⊤L Z (fsub⁺ [] ⊤R (wk sub-wken N))

expand⁻ {a Q .⁻} N = fsub⁻ [] <> pL N -- fsub⁻ <> pL N
expand⁻ {↑ A} N = fsub⁻ [] <> (↑L (expand⁺ (↑R (hyp⁺ Z)))) N
expand⁻ {A ⊃ B} N =
  ⊃R (expand⁺ {A} 
       (expand⁻ {B} 
         (fsub⁻ [] <> (⊃L (hyp⁺ Z) hyp⁻) 
           (wk' sub-wken (λ x → x) N)))) 
