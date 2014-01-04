
open import Prelude hiding (⊥)
open import Foc
open import Cut
open import Identity

module Admissible where

_⊢_ : Ctx → Conc → Set
Γ ⊢ U = Term Γ [] U

-- Initial rules

uinitsusp⁻ : ∀{Γ Q}
  → (Pers (a Q ⁻) :: Γ) ⊢ Susp (a Q ⁻)
uinitsusp⁻ = focL <> Z id⁻

uinit⁻ : ∀{Γ Q}
  → (Pers (a Q ⁻) :: Γ) ⊢ True (↓ (a Q ⁻))
uinit⁻ = focR (↓R (η⁻ (focL <> Z id⁻)))

uinitsusp⁺ : ∀{Γ Q}
  → (Susp (a Q ⁺) :: Γ) ⊢ True (a Q ⁺)
uinitsusp⁺ = focR (id⁺ Z)

uinit⁺ : ∀{Γ Q}
  → (Pers (↑ (a Q ⁺)) :: Γ) ⊢ True (a Q ⁺)
uinit⁺ = focL <> Z (↑L (η⁺ (focR (id⁺ Z))))

-- Disjunction

u⊥L : ∀{Γ U} → stable U
  → (Pers (↑ ⊥) :: Γ) ⊢ U
u⊥L pf = focL pf Z (↑L ⊥L)


u∨R₁ : ∀{Γ A B} → suspnormalΓ Γ
  → Γ ⊢ True A
  → Γ ⊢ True (A ∨ B)
u∨R₁ pfΓ N₁ = lsubst pfΓ (, <>) N₁ (expand⁺ (focR (∨R₁ (id⁺ Z))))

u∨R₂ : ∀{Γ A B} → suspnormalΓ Γ
  → Γ ⊢ True B
  → Γ ⊢ True (A ∨ B)
u∨R₂ pfΓ N₂ = lsubst pfΓ (, <>) N₂ (expand⁺ (focR (∨R₂ (id⁺ Z))))

u∨L : ∀{Γ A B U} → suspnormalΓ Γ → suspstable U
  → (Pers (↑ A) :: Γ) ⊢ U
  → (Pers (↑ B) :: Γ) ⊢ U
  → (Pers (↑ (A ∨ B)) :: Γ) ⊢ U
u∨L pfΓ pf N₁ N₂ = 
  focL (fst pf) Z 
    (↑L (lsubst (conspers pfΓ) pf Nid (∨L (↓L (wkex N₁)) (↓L (wkex N₂)))))
 where
  Nid = ∨L (expand⁺ (focR (∨R₁ (↓R (↑R (focR (id⁺ Z))))))) 
          (expand⁺ (focR (∨R₂ (↓R (↑R (focR (id⁺ Z))))))) 

-- Positive conjunction

u⊤⁺R : ∀{Γ} 
  → Γ ⊢ True ⊤⁺
u⊤⁺R = focR ⊤⁺R

u⊤⁺L : ∀{Γ U} → stable U
  → Γ ⊢ U
  → (Pers (↑ ⊤⁺) :: Γ) ⊢ U
u⊤⁺L pf N₁ = focL pf Z (↑L (⊤⁺L (wken N₁)))

u∧⁺R : ∀{Γ A B} → suspnormalΓ Γ 
  → Γ ⊢ True A 
  → Γ ⊢ True B 
  → Γ ⊢ True (A ∧⁺ B)
u∧⁺R pfΓ N₁ N₂ = 
  rsubst [] pfΓ <> (↑R N₁) (lsubst (conspers pfΓ) (, <>) (wken N₂) Nid)
 where
  Nid = expand⁺ (focL <> (S Z) (↑L (expand⁺ (focR (∧⁺R (id⁺ Z) (id⁺ (S Z)))))))

u∧⁺L : ∀{Γ A B U} → suspnormalΓ Γ → suspstable U 
  → (Pers (↑ B) :: Pers (↑ A) :: Γ) ⊢ U
  → (Pers (↑ (A ∧⁺ B)) :: Γ) ⊢ U
u∧⁺L pfΓ pf N₁ = 
  focL (fst pf) Z 
    (↑L (lsubst (conspers pfΓ) pf Nid (∧⁺L (↓L (↓L (wkex2 N₁))))))
 where
  Nid = ∧⁺L (expand⁺ (expand⁺ (focR (∧⁺R (↓R (↑R (focR (id⁺ (S Z))))) 
                                            (↓R (↑R (focR (id⁺ Z)))))))) 

-- Implication

u⊃R : ∀{Γ A B} → suspnormalΓ Γ 
  → (Pers (↑ A) :: Γ) ⊢ True (↓ B)
  → Γ ⊢ True (↓ (A ⊃ B))
u⊃R pfΓ N₁ = focR (↓R (rsubst [] pfΓ <> (⊃R (↓L (↑R N₁))) Nid)) 
 where
  Nid = ⊃R (expand⁺ 
              (expand⁻ 
                 (focL <> (S Z)  
                    (⊃L (↓R (↑R (focR (id⁺ Z))))
                       (↑L (↓L (focL <> Z id⁻)))))))

u⊃L : ∀{Γ A B U} → suspnormalΓ Γ → suspstable U 
  → Γ ⊢ True A 
  → (Pers B :: Γ) ⊢ U
  → (Pers (A ⊃ B) :: Γ) ⊢ U
u⊃L pfΓ pf N₁ N₂ = 
  lsubst (conspers pfΓ) pf 
    (lsubst (conspers pfΓ) (, <>) (wken N₁) Nid)
    (↓L (wkex N₂))
 where
  Nid = expand⁺ (focR (↓R (expand⁻ (focL <> (S Z) (⊃L (id⁺ Z) id⁻)))))

-- Negative conjunction

u⊤⁻R : ∀{Γ} 
  → Γ ⊢ True (↓ ⊤⁻)
u⊤⁻R = focR (↓R ⊤⁻R)

u∧⁻R : ∀{Γ A B} → suspnormalΓ Γ
  → Γ ⊢ True (↓ A)
  → Γ ⊢ True (↓ B)
  → Γ ⊢ True (↓ (A ∧⁻ B))
u∧⁻R pfΓ N₁ N₂ = 
  focR (↓R (rsubst [] pfΓ <> (∧⁻R (↑R N₁) (↑R N₂)) Nid))
 where
  Nid = ∧⁻R (expand⁻ (focL <> Z (∧⁻L₁ (↑L (↓L (focL <> Z id⁻))))))
          (expand⁻ (focL <> Z (∧⁻L₂ (↑L (↓L (focL <> Z id⁻))))))

u∧⁻L₁ : ∀{Γ A B U} → suspnormalΓ Γ → suspnormal U
  → (Pers A :: Γ) ⊢ U
  → (Pers (A ∧⁻ B) :: Γ) ⊢ U
u∧⁻L₁ pfΓ pf N₁ = 
  rsubst [] (conspers pfΓ) pf (expand⁻ (focL <> Z (∧⁻L₁ id⁻))) (wkex N₁)

u∧⁻L₂ : ∀{Γ A B U} → suspnormalΓ Γ → suspnormal U
  → (Pers B :: Γ) ⊢ U
  → (Pers (A ∧⁻ B) :: Γ) ⊢ U
u∧⁻L₂ pfΓ pf N₁ = 
  rsubst [] (conspers pfΓ) pf (expand⁻ (focL <> Z (∧⁻L₂ id⁻))) (wkex N₁)

-- Shift removal

u↓↑R : ∀{Γ A} 
  → Γ ⊢ True A
  → Γ ⊢ True (↓ (↑ A))
u↓↑R N₁ = focR (↓R (↑R N₁))

u↑↓L : ∀{Γ A U} → stable U
  → (Pers A :: Γ) ⊢ U
  → (Pers (↑ (↓ A)) :: Γ) ⊢ U
u↑↓L pf N₁ = focL pf Z (↑L (↓L (wkex N₁)))

