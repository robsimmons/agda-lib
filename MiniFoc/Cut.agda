
open import Prelude hiding (⊥; ⊤)
open import MiniFoc.Foc

module MiniFoc.Cut where

lsubst : ∀{A Γ C}
  → Reg C stable
  → Term [] Γ (Reg A) 
  → Spine [] Γ A (Reg C) 
  → Term [] Γ (Reg C)

either : ∀{A B Γ} (Γ' : Ctx) → B ∈ (Γ' ++ A :: Γ) → (A ≡ B) + (B ∈ (Γ' ++ Γ))
either [] Z = Inl Refl
either [] (S x) = Inr x
either (A :: Γ') Z = Inr Z
either (A :: Γ') (S x) with either Γ' x
... | Inl Refl = Inl Refl
... | Inr x' = Inr (S x')


rsubst : ∀{Γ A Form} (Γ' : Ctx)
  → (Value [] Γ A + (∃ λ A' → (A ≡ ↓ A') × Term [] Γ (Reg A')))
  → Exp [] (Γ' ++ A :: Γ) Form
  → Exp [] (Γ' ++ Γ) Form

-- subst⁺ : ∀{Γ A C} → Value [] Γ A → Term [] (A :: Γ) (Reg C) → Term [] Γ (Reg C)

lsubst pf (↓L pf₁ x Sp) pL = ↓L pf₁ x Sp
lsubst pf (↓L pf₁ x Sp) (↑L N) = ↓L pf x {!Sp!}
lsubst pf (↓L () x Sp) (⊃L V Sp')
lsubst pf (⊥L x) Sp = {!!}
lsubst pf (∨L x N₁ N₂) Sp = {!!}
lsubst pf (⊤L x N) Sp = {!!}
lsubst pf (↑R V) (↑L N) = rsubst [] (Inl V) N
lsubst pf (⊃R N) (⊃L V Sp) = lsubst pf (rsubst [] (Inl V) N) Sp

rsubst Γ' N (↓L pf₁ x Sp) with either Γ' x
rsubst Γ' V (↓L pf₁ x Sp) | Inl Refl = {!!}
... | Inr x' = ↓L pf₁ x' (rsubst Γ' N Sp)

rsubst Γ' N (hyp⁺ ())
rsubst Γ' N (pR x) with either Γ' x
rsubst Γ' N (pR x) | Inl Refl = ? -- pR (LIST.SET.sub-appendl _ Γ' x')
... | Inr x' = pR x'

rsubst Γ' N (↓R N') = ↓R (rsubst Γ' N N')
rsubst Γ' N (∨R₁ V) = ∨R₁ (rsubst Γ' N V)
rsubst Γ' N (∨R₂ V) = ∨R₂ (rsubst Γ' N V)
rsubst Γ' N ⊤R = ⊤R

rsubst Γ' N (⊥L x) with either Γ' x
rsubst Γ' N (⊥L x) | Inl Refl = ?
... | Inr x' = ⊥L x'

rsubst Γ' N (∨L x N₁ N₂) with either Γ' x
rsubst Γ' N (∨L x N₁ N₂) | Inl Refl = ?
{- (hyp⁺ ()) (∨L x N₁ N₂) | Inl Refl 
rsubst Γ' (∨R₁ V) (∨L x N₁ N₂) | Inl Refl = 
  rsubst [] (wk (LIST.SET.sub-appendl _ Γ') V) (rsubst (_ :: Γ') (∨R₁ V) N₁)
rsubst Γ' (∨R₂ V) (∨L x N₁ N₂) | Inl Refl =
  rsubst [] (wk (LIST.SET.sub-appendl _ Γ') V) (rsubst (_ :: Γ') (∨R₂ V) N₂) -}
... | Inr x' = ∨L x' (rsubst (_ :: Γ') N N₁) (rsubst (_ :: Γ') N N₂)

rsubst Γ' N (⊤L x N') with either Γ' x
rsubst Γ' N (⊤L x N') | Inl Refl = ?
... | Inr x' = ⊤L x' (rsubst Γ' N N')

rsubst Γ' N (↑R V) = ↑R {!!} -- rfoc pf (rsubst Γ' N V)
rsubst Γ' N (⊃R N') = ⊃R (rsubst (_ :: Γ') N N')

rsubst Γ' N hyp⁻ = hyp⁻
rsubst Γ' N pL = pL
rsubst Γ' N (↑L N') = ↑L (rsubst (_ :: Γ') N N')
rsubst Γ' N (⊃L V Sp) = ⊃L (rsubst Γ' N V) (rsubst Γ' N Sp)
