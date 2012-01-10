open import Prelude hiding (⊥; ⊤)
open import BabyFoc.Foc

module BabyFoc.Eta where

fsubN : ∀{Γ A U} (Γ' : List Type) 
  → U stable
  → Γ ⊢ A > U
  → (Γ' ++ Γ) ⊢ (Abs A) inv
  → (Γ' ++ Γ) ⊢ U inv

fsubSp : ∀{Γ A U B} (Γ' : List Type) 
  → U stable
  → Γ ⊢ A > U
  → (Γ' ++ Γ) ⊢ B > (Abs A)
  → (Γ' ++ Γ) ⊢ B > U 

fsubN Γ' pf Sp (foc pf₁ x pf₂ Sp') = foc pf x pf₂ (fsubSp Γ' pf Sp Sp')
fsubN Γ' pf Sp (⊥L x) = ⊥L x

fsubSp Γ' pf Sp hyp = wkSp (LIST.SET.sub-appendl _ Γ') Sp
fsubSp Γ' pf Sp (↑L pf' N) = ↑L pf' (fsubN (_ :: Γ') pf Sp N)
fsubSp Γ' pf Sp (⊃L V Sp') = ⊃L V (fsubSp Γ' pf Sp Sp')

expand⁻ : ∀{A Γ} → Γ ⊢ Abs A inv → Γ ⊢ Reg A inv
expand⁺ : ∀{A Γ} → A ∈ Γ → Γ ⊢ A foc

expand⁻ {a Q ⁺} N = fsubN [] <> (↑L <<>> (rfoc <<>> (pR Z))) N
expand⁻ {a Q ⁻} N = fsubN [] <> pL N
expand⁻ {A ⊃ B} N =  
  ⊃R (expand⁻ {B} 
        (fsubN [] <> (⊃L (expand⁺ {A} Z) hyp) (wkN LIST.SET.sub-wken N)))
expand⁻ {⊥} N = fsubN [] <> (↑L <<>> (⊥L Z)) N
expand⁻ {⊤} N = rfoc <<>> ⊤R

expand⁺ {a Q ⁺} x = pR x
expand⁺ {a Q ⁻} x = ↓R <> (foc <> x <> pL)
expand⁺ {A ⊃ B} x = 
  ↓R <> (⊃R (expand⁻ {B} (foc <> (S x) <> (⊃L (expand⁺ {A} Z) hyp))))
expand⁺ {⊥} x = {!!}
expand⁺ {⊤} x = ⊤R

identity : ∀{A Γ} → A ∈ Γ → Γ ⊢ Reg A inv
identity {a Q ⁺} x = rfoc <<>> (pR x)
identity {a Q ⁻} x = expand⁻ (foc <> x <> hyp)
identity {A ⊃ B} x = expand⁻ (foc <> x <> hyp)
identity {⊥} x = ⊥L x
identity {⊤} x = rfoc <<>> ⊤R
