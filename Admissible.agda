
open import Prelude hiding (⊥)
open import Foc
open import Cut
open import Identity

module Admissible where

_⊢_ : Ctx → Type ⁻ → Set
Γ ⊢ A = Term [] Γ [] (Reg A)

↓↑ : Type ⁺ → Type ⁺
↓↑ A = ↓ (↑ A)

-- Initial rules

un↑↓ : ∀{Γ A} → Γ ⊢ (↑ (↓ A)) → Γ ⊢ A
un↑↓ N = rsubstN [] N (expand⁻ (↓L <> Z (↑L (L <> (↓L <> Z hyp⁻)))))

uinit⁻ : ∀{Γ Q} → (↓ (a Q ⁻) :: Γ) ⊢ (a Q ⁻)
uinit⁻ = ↓L <> Z pL

uinit⁺₁ : ∀{Γ Q} → (↓ (↑ (a Q ⁺)) :: Γ) ⊢ (↑ (a Q ⁺))
uinit⁺₁ = ↓L <> Z (↑L (L <> (↑R (pR Z))))

uinit⁺₂ : ∀{Γ Q} → a Q ⁺ ∈ Γ → Γ ⊢ (↑ (a Q ⁺))
uinit⁺₂ x = ↑R (pR x)

-- Disjunction

u⊥L : ∀{Γ C} → (↓↑ ⊥ :: Γ) ⊢ C
u⊥L = un↑↓ (↓L <> Z (↑L ⊥L))

u∨R₁ : ∀{Γ A B} → Γ ⊢ ↑ A → Γ ⊢ ↑ (A ∨ B)
u∨R₁ N₁ = subst⁻ <> N₁ (↑L (expand⁺ (↑R (∨R₁ (hyp⁺ Z)))))

u∨R₂ : ∀{Γ A B} → Γ ⊢ ↑ B → Γ ⊢ ↑ (A ∨ B)
u∨R₂ N₂ = subst⁻ <> N₂ (↑L (expand⁺ (↑R (∨R₂ (hyp⁺ Z)))))

u∨L : ∀{Γ A B C} → (↓↑ A :: Γ) ⊢ C → (↓↑ B :: Γ) ⊢ C → (↓↑ (A ∨ B) :: Γ) ⊢ C
u∨L N₁ N₂ =
  un↑↓ (↓L <> Z (↑L (lsubstN (_ :: []) <> Nid 
                   (∨L (L <> (↑R (↓R (wk LIST.SET.sub-wkex N₁)))) 
                      (L <> (↑R (↓R (wk LIST.SET.sub-wkex N₂))))))))
 where
  Nid = ∨L (expand⁺ (↑R (∨R₁ (↓R (↑R (hyp⁺ Z)))))) 
          (expand⁺ (↑R (∨R₂ (↓R (↑R (hyp⁺ Z)))))) 

-- Positive conjunction

u⊤⁺R : ∀{Γ} → Γ ⊢ ↑ ⊤⁺
u⊤⁺R = ↑R ⊤⁺R

u⊤⁺L : ∀{Γ C} → Γ ⊢ C → (↓↑ ⊤⁺ :: Γ) ⊢ C
u⊤⁺L N₁ = un↑↓ (↓L <> Z (↑L (⊤⁺L (↑R (↓R (wk LIST.SET.sub-wken N₁)))))) 

u∧⁺R : ∀{Γ A B} → Γ ⊢ ↑ A → Γ ⊢ ↑ B → Γ ⊢ ↑ (A ∧⁺ B)
u∧⁺R N₁ N₂ = 
  rsubstN [] N₂
    (subst⁻ <> (wk LIST.SET.sub-wken N₁) 
      (↑L (expand⁺ (↓L <> Z (↑L (expand⁺ (↑R (∧⁺R (hyp⁺ (S Z)) (hyp⁺ Z)))))))))

u∧⁺L : ∀{Γ A B C} → (↓↑ B :: ↓↑ A :: Γ) ⊢ C → (↓↑ (A ∧⁺ B) :: Γ) ⊢ C
u∧⁺L N₁ = 
  un↑↓ (↓L <> Z 
          (↑L (lsubstN (_ :: []) <> Nid 
                 (∧⁺L (L <> (L <> (↑R (↓R (wk (θ LIST.SET.sub-wkex) N₁)))))))))
 where 
  Nid = ∧⁺L (expand⁺
              (expand⁺ (↑R (∧⁺R (↓R (↑R (hyp⁺ (S Z)))) (↓R (↑R (hyp⁺ Z)))))))
  θ = LIST.SET.sub-cons-congr

-- Implication

u⊃R : ∀{Γ A B} → (↓↑ A :: Γ) ⊢ B → Γ ⊢ (A ⊃ B)
u⊃R N₁ = rsubstN [] (⊃R (L <> N₁)) 
           (⊃R (expand⁺ (expand⁻ (↓L <> Z (⊃L (↓R (↑R (hyp⁺ Z))) hyp⁻)))))

u⊃L : ∀{Γ A B C} → Γ ⊢ ↑ A → (↓ B :: Γ) ⊢ C → (↓ (A ⊃ B) :: Γ) ⊢ C
u⊃L N₁ N₂ = un↑↓ (subst⁻ <> (subst⁻ <> (wk LIST.SET.sub-wken N₁) (↑L Nid))
                   (↑L (L <> (↑R (↓R (wk LIST.SET.sub-wkex N₂))))))
 where
  Nid = expand⁺ (↑R (↓R (expand⁻ (↓L <> Z (⊃L (hyp⁺ Z) hyp⁻)))))

-- Negative conjunction

u⊤⁻R : ∀{Γ} → Γ ⊢ ⊤⁻
u⊤⁻R = ⊤⁻R

u∧⁻R : ∀{Γ A B} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ (A ∧⁻ B)
u∧⁻R N₁ N₂ = ∧⁻R N₁ N₂

u∧⁻L₁ : ∀{Γ A B C} → (↓ A :: Γ) ⊢ C → (↓ (A ∧⁻ B) :: Γ) ⊢ C
u∧⁻L₁ N₁ = rsubstN [] (expand⁻ (↓L <> Z (∧⁻L₁ hyp⁻))) (wk LIST.SET.sub-wkex N₁)

u∧⁻L₂ : ∀{Γ A B C} → (↓ B :: Γ) ⊢ C → (↓ (A ∧⁻ B) :: Γ) ⊢ C
u∧⁻L₂ N₂ = rsubstN [] (expand⁻ (↓L <> Z (∧⁻L₂ hyp⁻))) (wk LIST.SET.sub-wkex N₂)

-- Shift removal

u↑↓L : ∀{Γ A C} → ((↓ A) :: Γ) ⊢ C → (↓ (↑ (↓ A)) :: Γ) ⊢ C
u↑↓L N₁ = un↑↓ (↓L <> Z (↑L (L <> (↑R (↓R (wk LIST.SET.sub-wkex N₁))))))

u↑↓R : ∀{Γ A} → Γ ⊢ A → Γ ⊢ ↑ (↓ A)
u↑↓R N₁ = ↑R (↓R N₁)