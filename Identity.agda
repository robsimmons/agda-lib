
open import Prelude hiding (⊥; ⊤)
open import Foc

module Identity where

-- Focal substitution

-- Values for value variables

fsub⁺ : ∀{א Γ A Form} → Value א Γ A → Exp (A :: א) Γ Form → Exp א Γ Form

fsub⁺ V (hyp⁺ Z) = V
fsub⁺ V (hyp⁺ (S n)) = hyp⁺ n
fsub⁺ V (pR x) = pR x
fsub⁺ V (↓R N) = ↓R (fsub⁺ V N)
fsub⁺ V (∨R₁ V') = ∨R₁ (fsub⁺ V V')
fsub⁺ V (∨R₂ V') = ∨R₂ (fsub⁺ V V')
fsub⁺ V ⊤⁺R = ⊤⁺R
fsub⁺ V (∧⁺R V₁ V₂) = ∧⁺R (fsub⁺ V V₁) (fsub⁺ V V₂)

fsub⁺ V (L pf⁺ N) = L pf⁺ (fsub⁺ (wk LIST.SET.sub-wken V) N)
fsub⁺ V (↓L pf⁻ x Sp) = ↓L pf⁻ x (fsub⁺ V Sp)
fsub⁺ V ⊥L = ⊥L
fsub⁺ V (∨L N₁ N₂) = ∨L (fsub⁺ V N₁) (fsub⁺ V N₂)
fsub⁺ V (⊤⁺L N) = ⊤⁺L (fsub⁺ V N)
fsub⁺ V (∧⁺L N) = ∧⁺L (fsub⁺ V N)
fsub⁺ V (↑R V') = ↑R (fsub⁺ V V')
fsub⁺ V (⊃R N) = ⊃R (fsub⁺ V N)
fsub⁺ V ⊤⁻R = ⊤⁻R
fsub⁺ V (∧⁻R N₁ N₂) = ∧⁻R (fsub⁺ V N₁) (fsub⁺ V N₂)

fsub⁺ V hyp⁻ = hyp⁻
fsub⁺ V pL = pL
fsub⁺ V (↑L N) = ↑L (fsub⁺ V N)
fsub⁺ V (⊃L V' Sp) = ⊃L (fsub⁺ V V') (fsub⁺ V Sp)
fsub⁺ V (∧⁻L₁ Sp) = ∧⁻L₁ (fsub⁺ V Sp)
fsub⁺ V (∧⁻L₂ Sp) = ∧⁻L₂ (fsub⁺ V Sp)

-- Spines for spine variables

fsub⁻ : ∀{א Γ A Ω U} 
  → U stable⁻
  → Spine א Γ A U
  → Term א Γ Ω (Abs A)
  → Term א Γ Ω U 

fsubSp⁻ : ∀{א Γ A U B}
  → U stable⁻
  → Spine א Γ A U
  → Spine א Γ B (Abs A)
  → Spine א Γ B U 

fsub⁻ pf Sp (L pf⁺ N) = L pf⁺ (fsub⁻ pf (wk LIST.SET.sub-wken Sp) N)
fsub⁻ pf Sp (↓L pf⁻ x Sp') = ↓L pf x (fsubSp⁻ pf Sp Sp')
fsub⁻ pf Sp ⊥L = ⊥L
fsub⁻ pf Sp (∨L N₁ N₂) = ∨L (fsub⁻ pf Sp N₁) (fsub⁻ pf Sp N₂)
fsub⁻ pf Sp (⊤⁺L N) = ⊤⁺L (fsub⁻ pf Sp N)
fsub⁻ pf Sp (∧⁺L N) = ∧⁺L (fsub⁻ pf Sp N)

fsubSp⁻ pf Sp hyp⁻ = Sp
fsubSp⁻ pf Sp (↑L N) = ↑L (fsub⁻ pf Sp N)
fsubSp⁻ pf Sp (⊃L V Sp') = ⊃L V (fsubSp⁻ pf Sp Sp')
fsubSp⁻ pf Sp (∧⁻L₁ Sp') = ∧⁻L₁ (fsubSp⁻ pf Sp Sp')
fsubSp⁻ pf Sp (∧⁻L₂ Sp') = ∧⁻L₂ (fsubSp⁻ pf Sp Sp')

-- Identity expansion

expand⁺ : ∀{A א Γ Ω U} → Term (A :: א) Γ Ω U → Term א Γ (A :: Ω) U
expand⁻ : ∀{A א Γ} → Term א Γ [] (Abs A) → Term א Γ [] (Reg A)

expand⁺ {a Q .⁺} N = L <> (fsub⁺ (pR Z) (wk LIST.SET.sub-wken N))
expand⁺ {↓ A} N = 
  L <> (fsub⁺ (↓R (expand⁻ (↓L <> Z hyp⁻))) (wk LIST.SET.sub-wken N)) 
expand⁺ {⊥} N = ⊥L 
expand⁺ {A ∨ B} N = 
  ∨L (expand⁺ (fsub⁺ (∨R₁ (hyp⁺ Z)) (fwk LIST.SET.sub-wkex N)))
    (expand⁺ (fsub⁺ (∨R₂ (hyp⁺ Z)) (fwk LIST.SET.sub-wkex N)))
expand⁺ {⊤⁺} N = ⊤⁺L (fsub⁺ ⊤⁺R N)
expand⁺ {A ∧⁺ B} N = 
  ∧⁺L (expand⁺
        (expand⁺
          (fsub⁺ (∧⁺R (hyp⁺ (S Z)) (hyp⁺ Z))
            (fwk LIST.SET.sub-wkex (fwk LIST.SET.sub-wkex N)))))

expand⁻ {a Q .⁻} N = fsub⁻ <> pL N
expand⁻ {↑ A} N = fsub⁻ <> (↑L (expand⁺ (↑R (hyp⁺ Z)))) N
expand⁻ {A ⊃ B} N = 
  ⊃R (expand⁺ 
       (expand⁻ 
         (fsub⁻ <> (⊃L (hyp⁺ Z) hyp⁻) (fwk LIST.SET.sub-wken N))))
expand⁻ {⊤⁻} N = ⊤⁻R
expand⁻ {A ∧⁻ B} N =
  ∧⁻R (expand⁻ (fsub⁻ <> (∧⁻L₁ hyp⁻) N)) (expand⁻ (fsub⁻ <> (∧⁻L₂ hyp⁻) N))