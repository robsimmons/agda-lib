open import Prelude hiding (Level; _≤_)

module Adjoint 
  (Level : Set)
  (True : Level)
  (_≤_ : Level → Level → Set)
  (refl≤ : (L : Level) → L ≤ L)
  (trans≤ : ∀{L1 L2 L3} → L1 ≤ L2 → L2 ≤ L3 → L1 ≤ L3)
  (truth : (L : Level) → True ≤ L)
  (dec≤ : (L1 L2 : Level) → Decidable (L1 ≤ L2)) where

-- Polarized logic

data Polarity : Set where
  ⁺ : Polarity
  ⁻ : Polarity

data Type : Polarity → Set where
  q : (Q : String) {⁼ : Polarity} → Type ⁼
  --
  ↓ : (P : Type ⁻) → Type ⁺
  ! : (L : Level) (A : Type ⁺) → Type ⁺ 
  -- ⊥ : Type ⁺
  -- _∨_ : (A B : Type ⁺) → Type ⁺
  -- ⊤⁺ : Type ⁺
  ↑ : (P : Type ⁺) → Type ⁻
  _⊃_ : (A : Type ⁺) (B : Type ⁻) → Type ⁻
  ⊤⁻ : Type ⁻
  _∧⁻_ : (A B : Type ⁻) → Type ⁻


-- Contexts and operations on them (context clearing)

_⊆_ : ∀{A} → List A → List A → Set
_⊆_ = LIST.SET.Sub

Hyp = Type ⁺ × Level
Ctx = List Hyp

clear : Ctx → Level → Ctx
clear [] L = []
clear ((A , L') :: Γ) L with dec≤ L L'
... | Inl _ = (A , L') :: clear Γ L
... | Inr _ = clear Γ L

-- L ≤ L' and (A , L') ∈ Γ is necessary and sufficient for (A , L') ∈ clear Γ L

inclear-necc : ∀{Γ L H} → H ∈ clear Γ L → (L ≤ (snd H)) × (H ∈ Γ)
inclear-necc {[]} ()
inclear-necc {H :: Γ} {L} x with dec≤ L (snd H)
inclear-necc {H :: Γ} Z | Inl inl = (inl , Z)
inclear-necc {H :: Γ} (S n) | Inl inl = 
  fst (inclear-necc {Γ} n) , S (snd (inclear-necc {Γ} n))
inclear-necc {H :: Γ} {L} x | Inr _ =
  fst (inclear-necc {Γ} x) , S (snd (inclear-necc {Γ} x))

inclear-suff : ∀{Γ L L' A} → L ≤ L' → (A , L') ∈ Γ → (A , L') ∈ clear Γ L
inclear-suff {[]} pf≤ ()
inclear-suff {H :: Γ} {L} pf≤ Z with dec≤ L (snd H)
... | Inl _ = Z
... | Inr pf = abort (pf pf≤)
inclear-suff {H :: Γ} {L} pf≤ (S n) with dec≤ L (snd H)
... | Inl _ = S (inclear-suff pf≤ n)
... | Inr _ = inclear-suff pf≤ n

clear⊆ : ∀{Γ L Γ'} → Γ ⊆ Γ' → clear Γ L ⊆ clear Γ' L
clear⊆ {Γ} {L} {Γ'} θ x = 
  inclear-suff {Γ'} (fst (inclear-necc {Γ} x)) (θ (snd (inclear-necc {Γ} x)))

cleartrue : ∀{Γ} → Γ ≡ clear Γ True
cleartrue {[]} = refl
cleartrue {(A , L) :: Γ} with dec≤ True L
... | Inl _ = LIST.cons-congr (cleartrue {Γ})
... | Inr pf = abort (pf (truth _))

clearlem : ∀{Γ L1 L2} → L1 ≤ L2 → clear Γ L2 ≡ clear (clear Γ L1) L2
clearlem {[]} pf = refl
clearlem {(A , L') :: Γ} {L1} {L2} pf with dec≤ L1 L' | dec≤ L2 L' 
clearlem {(A , L') :: Γ} {L1} {L2} pf | Inl pf1 | Inl pf2 with dec≤ L2 L'
clearlem {(A , L') :: Γ} {L1} {L2} pf | Inl pf1 | Inl pf2 | Inl _ = 
  LIST.cons-congr (clearlem {Γ} pf)
clearlem {(A , L') :: Γ} {L1} {L2} pf | Inl pf1 | Inl pf2 | Inr pf' = 
  abort (pf' pf2)
clearlem {(A , L') :: Γ} {L1} {L2} pf | Inl pf1 | Inr pf2 with dec≤ L2 L'
clearlem {(A , L') :: Γ} {L1} {L2} pf | Inl pf1 | Inr pf2 | Inl pf' = 
  abort (pf2 pf')
clearlem {(A , L') :: Γ} {L1} {L2} pf | Inl pf1 | Inr pf2 | Inr pf' = 
  clearlem {Γ} pf
clearlem {(A , L') :: Γ} {L1} {L2} pf | Inr pf1 | Inl pf2 = 
  abort (pf1 (trans≤ pf pf2))
clearlem {(A , L') :: Γ} {L1} {L2} pf | Inr pf1 | Inr pf2 = clearlem {Γ} pf

clearer : ∀{Γ L1 L2} → L1 ≤ L2 → clear Γ L2 ⊆ clear (clear Γ L1) L2
clearer {Γ} pf = LIST.SET.sub-eq (clearlem {Γ} pf)

clearer' : ∀{Γ L L'} → L ≤ L' → clear (clear Γ L) L' ⊆ clear Γ L'
clearer' {Γ} pf = LIST.SET.sub-eq (symm (clearlem {Γ} pf))


-- Propositions

data Conc : Set where
  Cont : (A : Type ⁻) → Conc
  Reg : (A : Type ⁻) → Conc

_stable⁻ : Conc → Set
Cont A stable⁻ = Unit
Reg (q Q) stable⁻ = Unit
Reg (↑ P) stable⁻ = Unit
Reg (A ⊃ B) stable⁻ = Void
Reg ⊤⁻ stable⁻ = Void
Reg (A ∧⁻ B) stable⁻ = Void

_stable⁺ : Hyp → Set
(q Q , L) stable⁺ = Unit
(↓ P , L) stable⁺ = Unit
(! L' A , L) stable⁺ = Void

data SeqForm : Set where
  Rfoc : Hyp → SeqForm
  Inv : Maybe Hyp → Conc → SeqForm 
  Lfoc : Type ⁻ → Conc → SeqForm

data Exp (א Γ : Ctx) : SeqForm → Set

Value : Ctx → Ctx → Hyp → Set
Value א Γ A = Exp א Γ (Rfoc A)

Case : Ctx → Ctx → Hyp → Conc → Set
Case א Γ Ω U = Exp א Γ (Inv (Just Ω) U)

Term : Ctx → Ctx → Conc → Set
Term א Γ U = Exp א Γ (Inv Nothing U)

Spine : Ctx → Ctx → Type ⁻ → Conc → Set
Spine א Γ A U = Exp א Γ (Lfoc A U)

data Exp א Γ where

  -- Values
  hyp⁺ : ∀{H}
    (v : H ∈ א)
    → Value א Γ H
  pR : ∀{Q L}
    (x : (q Q , L) ∈ Γ)
    → Value א Γ (q Q , L)
  ↓R : ∀{A L}
    (N : Term א Γ (Reg A))
    → Value א Γ (↓ A , L)
  !R : ∀{L1 L2 A}
    (pf≤ : L1 ≤ L2)
    (V : Value (clear א L2) (clear Γ L2) (A , L2))
    → Value א Γ (! L2 A , L1)
  
  -- Terms
  L : ∀{H U}
    (pf⁺ : H stable⁺)
    (N : Term א (H :: Γ) U)
    → Case א Γ H U
  ↓L : ∀{A U L}
    (pf⁻ : U stable⁻)
    (x : (↓ A , L) ∈ Γ)
    (Sp : Spine א Γ A U)
    → Term א Γ U
  !L : ∀{A U L1 L2} 
    (NI : L1 ≤ L2 → Case א Γ (A , L2) U)
    → Case א Γ (! L2 A , L1) U 
  ↑R : ∀{A}
    (V : Value א Γ (A , True))
    → Term א Γ (Reg (↑ A))
  ⊃R : ∀{A B}
    (NI : Case א Γ (A , True) (Reg B))
    → Term א Γ (Reg (A ⊃ B))
  ⊤⁻R : Term א Γ (Reg ⊤⁻)
  ∧⁻R : ∀{A B}
    (N₁ : Term א Γ (Reg A))
    (N₂ : Term א Γ (Reg B))
    → Term א Γ (Reg (A ∧⁻ B))

  -- Spines
  hyp⁻ : ∀{A}
    → Spine א Γ A (Cont A)
  pL : ∀{Q}
    → Spine א Γ (q Q) (Reg (q Q))
  ↑L : ∀{A U}
    (NI : Case א Γ (A , True) U)
    → Spine א Γ (↑ A) U
  ⊃L : ∀{A B U}
    (V : Value א Γ (A , True))
    (Sp : Spine א Γ B U)
    → Spine א Γ (A ⊃ B) U
  ∧⁻L₁ : ∀{A B U}
    (Sp : Spine א Γ A U)
    → Spine א Γ (A ∧⁻ B) U
  ∧⁻L₂ : ∀{A B U}
    (Sp : Spine א Γ B U)
    → Spine א Γ (A ∧⁻ B) U



-- Weakening

wk' : ∀{א א' Γ Γ' Form} → א ⊆ א' → Γ ⊆ Γ' → Exp א Γ Form → Exp א' Γ' Form

wk' ρ θ (hyp⁺ v) = hyp⁺ (ρ v)
wk' ρ θ (pR x) = pR (θ x)
wk' ρ θ (↓R N) = ↓R (wk' ρ θ N)
wk' ρ θ (!R pf≤ V) = !R pf≤ (wk' (clear⊆ ρ) (clear⊆ θ) V)

wk' ρ θ (L pf⁺ N) = L pf⁺ (wk' ρ (LIST.SET.sub-cons-congr θ) N)
wk' ρ θ (↓L pf⁻ x Sp) = ↓L pf⁻ (θ x) (wk' ρ θ Sp)
wk' ρ θ (!L NI) = !L (λ pf → wk' ρ θ (NI pf))
wk' ρ θ (↑R V) = ↑R (wk' ρ θ V)
wk' ρ θ (⊃R NI) = ⊃R (wk' ρ θ NI)
wk' ρ θ ⊤⁻R = ⊤⁻R
wk' ρ θ (∧⁻R N₁ N₂) = ∧⁻R (wk' ρ θ N₁) (wk' ρ θ N₂)

wk' ρ θ hyp⁻ = hyp⁻
wk' ρ θ pL = pL
wk' ρ θ (↑L NI) = ↑L (wk' ρ θ NI)
wk' ρ θ (⊃L V Sp) = ⊃L (wk' ρ θ V) (wk' ρ θ Sp)
wk' ρ θ (∧⁻L₁ Sp) = ∧⁻L₁ (wk' ρ θ Sp)
wk' ρ θ (∧⁻L₂ Sp) = ∧⁻L₂ (wk' ρ θ Sp)

wk : ∀{א Γ Γ' Form} → Γ ⊆ Γ' → Exp א Γ Form → Exp א Γ' Form
wk = wk' (λ x → x)

fwk : ∀{א א' Γ Form} → א ⊆ א' → Exp א Γ Form → Exp א' Γ Form
fwk ρ = wk' ρ (λ x → x)



-- Focal substitution (positive)

fsub⁺ : ∀{א Γ Form A L} 
  → Value (clear א L) (clear Γ L) (A , L)
  → Exp ((A , L) :: א) Γ Form 
  → Exp א Γ Form

fsub⁺ V (hyp⁺ Z) = wk' (snd o inclear-necc) (snd o inclear-necc) V
fsub⁺ V (hyp⁺ (S v)) = hyp⁺ v
fsub⁺ V (pR x) = pR x
fsub⁺ V (↓R N) = ↓R (fsub⁺ V N)
fsub⁺ {א} {Γ} {L = L3} V (!R {L1} {L2} pf≤ V') with dec≤ L2 L3
... | Inl pf = !R pf≤ (fsub⁺ (wk' (clearer {א} pf) (clearer {Γ} pf) V) V') 
... | Inr pf = !R pf≤ V' 

fsub⁺ V (L pf⁺ N) = L pf⁺ (fsub⁺ (wk (clear⊆ LIST.SET.sub-wken) V) N)
fsub⁺ V (↓L pf⁻ x Sp) = ↓L pf⁻ x (fsub⁺ V Sp)
fsub⁺ V (!L NI) = !L (λ pf → fsub⁺ V (NI pf))
fsub⁺ V (↑R V') = ↑R (fsub⁺ V V')
fsub⁺ V (⊃R NI) = ⊃R (fsub⁺ V NI)
fsub⁺ V ⊤⁻R = ⊤⁻R
fsub⁺ V (∧⁻R N₁ N₂) = ∧⁻R (fsub⁺ V N₁) (fsub⁺ V N₂)

fsub⁺ V hyp⁻ = hyp⁻
fsub⁺ V pL = pL
fsub⁺ V (↑L NI) = ↑L (fsub⁺ V NI)
fsub⁺ V (⊃L V' Sp) = ⊃L (fsub⁺ V V') (fsub⁺ V Sp)
fsub⁺ V (∧⁻L₁ Sp) = ∧⁻L₁ (fsub⁺ V Sp)
fsub⁺ V (∧⁻L₂ Sp) = ∧⁻L₂ (fsub⁺ V Sp)



-- Focal substituion (negative)

fsub⁻ : ∀{א Γ A U} 
  → U stable⁻
  → Spine א Γ A U
  → Term א Γ (Cont A)
  → Term א Γ U

fsubNI⁻ : ∀{א Γ A U Ω} 
  → U stable⁻
  → Spine א Γ A U
  → Case א Γ Ω (Cont A)
  → Case א Γ Ω U

fsubSp⁻ : ∀{א Γ A U B} 
  → U stable⁻
  → Spine א Γ A U
  → Spine א Γ B (Cont A)
  → Spine א Γ B U

fsub⁻ pf⁻ Sp (↓L _ x Sp') = ↓L pf⁻ x (fsubSp⁻ pf⁻ Sp Sp')

fsubNI⁻ pf⁻ Sp (L pf⁺ N) = L pf⁺ (fsub⁻ pf⁻ (wk LIST.SET.sub-wken Sp) N)
fsubNI⁻ pf⁻ Sp (!L NI) = !L (λ pf → (fsubNI⁻ pf⁻ Sp (NI pf)))

fsubSp⁻ pf⁻ Sp hyp⁻ = Sp
fsubSp⁻ pf⁻ Sp (↑L NI) = ↑L (fsubNI⁻ pf⁻ Sp NI)
fsubSp⁻ pf⁻ Sp (⊃L V Sp') = ⊃L V (fsubSp⁻ pf⁻ Sp Sp')
fsubSp⁻ pf⁻ Sp (∧⁻L₁ Sp') = ∧⁻L₁ (fsubSp⁻ pf⁻ Sp Sp')
fsubSp⁻ pf⁻ Sp (∧⁻L₂ Sp') = ∧⁻L₂ (fsubSp⁻ pf⁻ Sp Sp')



-- Identity expansion

expand⁺ : ∀{A L א Γ U} → Term ((A , L) :: א) Γ U → Case א Γ (A , L) U

expand⁻ : ∀{A א Γ} → Term א Γ (Cont A) → Term א Γ (Reg A)

expand⁺ {q Q} N = 
  L <> (fsub⁺ (pR (inclear-suff (refl≤ _) Z)) 
    (wk LIST.SET.sub-wken N))
expand⁺ {↓ P} N = 
  L <> (fsub⁺ (↓R (expand⁻ (↓L <> (inclear-suff (refl≤ _) Z) hyp⁻)))
    (wk LIST.SET.sub-wken N))
expand⁺ { ! L2 A} {L1} {א} N = 
  !L (λ pf → expand⁺ (fsub⁺ (!R pf (hyp⁺ (inclear-suff (refl≤ _) (x pf))))
    (fwk LIST.SET.sub-wkex N)))
 where
   x : L1 ≤ L2 → (A , L2) ∈ clear ((A , L2) :: א) L1
   x pf with dec≤ L1 L2
   ... | Inl _ = Z
   ... | Inr pf' = abort (pf' pf)

expand⁻ {q Q} N = fsub⁻ <> pL N
expand⁻ {↑ P} N = fsub⁻ <> (↑L (expand⁺ (↑R (hyp⁺ Z)))) N
expand⁻ {A ⊃ B} N = 
  ⊃R (expand⁺ 
       (expand⁻ (fsub⁻ <> (⊃L (hyp⁺ Z) hyp⁻) (fwk LIST.SET.sub-wken N))))
expand⁻ {⊤⁻} N = ⊤⁻R
expand⁻ {A ∧⁻ B} N = 
  ∧⁻R (expand⁻ (fsub⁻ <> (∧⁻L₁ hyp⁻) N)) (expand⁻ (fsub⁻ <> (∧⁻L₂ hyp⁻) N))



