-- Constructive Provability Logic 
-- De-tethered intuitionstic variant
-- Robert J. Simmons, Bernardo Toninho

-- Equivalence of sequent calculus and natural deduction

open import Prelude hiding (⊥)
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import DetetheredCPL.Core renaming (Type to UType)
open import DetetheredCPL.NatDeduction
open import FocusedCPL.Core
open import FocusedCPL.Weakening
open import FocusedCPL.Atomic
open import FocusedCPL.Cut
open import FocusedCPL.Identity
-- open import DetetheredCPL.Sequent

module DetetheredCPL.Equiv where

module EQUIV 
  (UWF : UpwardsWellFounded)
  (dec≺ : (w w' : _) → Decidable (TRANS-UWF._≺*_ UWF w w')) where
  open TRANS-UWF UWF
  open ILIST UWF
  open CORE UWF renaming (MCtx to UMCtx)
  open NAT-DEDUCTION UWF
  open SEQUENT UWF
  open WEAKENING UWF
  open ATOMIC UWF
  open CUT UWF
  open IDENTITY UWF

  eraseA : ∀{⁼} → Type ⁼ → UType
  eraseA {⁼} (a Q .⁼) = a Q ⁼
  eraseA (↓ A) = eraseA A
  eraseA ⊥ = ⊥
  eraseA (◇ A) = ◇ (eraseA A)
  eraseA (□ A) = □ (eraseA A)
  eraseA (↑ A) = eraseA A
  eraseA (A ⊃ B) = eraseA A ⊃ eraseA B

  eraseΩ : ICtx → UMCtx
  eraseΩ · = []
  eraseΩ (I A w) = [ eraseA A at w ]

  eraseΓ : MCtx → UMCtx
  eraseΓ [] = []
  eraseΓ ((A at w) :: Γ) = (eraseA A at w) :: eraseΓ Γ

  erasex : ∀{A w Γ} → (A at w) ∈ Γ → (eraseA A at w) ∈ eraseΓ Γ
  erasex Z = Z
  erasex (S x) = S (erasex x)

  _stableΓ : MCtx → Set
  _stableΓ = LIST.All (λ Item → prjx Item stable⁺)

  Pfoc : W → Set
  Pfoc wc = ∀{Γ A}
    → Γ stableΓ
    → eraseΓ Γ ⊢ eraseA A [ wc ]
    → Term [] Γ wc · (Reg A)

  PdefocV : W → Set
  PdefocV wc = ∀{Γ A}
    → Γ stableΓ
    → Value [] Γ wc A
    → eraseΓ Γ ⊢ eraseA A [ wc ]

  PdefocN : W → Set
  PdefocN wc = ∀{Γ Ω A}
    → Γ stableΓ
    → wc ≺' Ω
    → Term [] Γ wc Ω (Reg A)
    → (eraseΩ Ω ++ eraseΓ Γ) ⊢ eraseA A [ wc ]

  PdefocSp : W → Set
  PdefocSp wc = ∀{Γ B A wh}
    → Γ stableΓ
    → wc ≺* wh
    → Spine [] Γ wh B wc (Reg A)
    → (eraseA B at wh :: eraseΓ Γ) ⊢ eraseA A [ wc ]


  record Pequiv (wc : W) : Set where
   field
    foc : Pfoc wc
    defocV : PdefocV wc
    defocN : PdefocN wc
    defocSp : PdefocSp wc

  module EQUIV-LEM (wc : W) (ih : (wc' : W) → wc ≺+ wc' → Pequiv wc') where

    defocV : PdefocV wc
    defocN : PdefocN wc
    defocSp : PdefocSp wc

    defocV pf (pR x) = hyp (erasex x)
    defocV pf (↓R N₁) = defocN pf · N₁
    defocV pf (◇R ω N₁) = ◇I ω (Pequiv.defocN (ih _ (≺+0 ω)) pf · N₁)
    defocV pf (□R N₁) = □I λ ω → Pequiv.defocN (ih _ (≺+0 ω)) pf · (N₁ ω)

    defocN pf ω (L pf⁺ N₁) = defocN (LIST.ALL.cons pf⁺ pf) · N₁
    defocN pf ω (↓L pf⁻ ωh x Sp) = 
      subst ωh (hyp (erasex x)) (defocSp pf ωh Sp)
    defocN pf (I ω) ⊥L = ⊥E ω (hyp Z)
    defocN pf (I ω) (◇L N₁) = ◇E ω (hyp Z) 
      λ ω' D₀ → ssubst (⊆pr/xtndR ⊆pr/refl 
                          (◇I ω' (WK-N.wkN 
                                    (⊆to/stenirrev (≺⊀ ω') (⊆to/refl _)) 
                                    D₀))) 
                   (defocN pf · (N₁ ω' {!D₀!}))
    defocN pf (I ω) (□L N₁) = □E ω (hyp Z) λ D₀ → {!!}
    defocN pf ω (↑R V₁) = defocV pf V₁
    defocN pf ω (⊃R N₁) = ⊃I (defocN pf (I ≺*≡) N₁)
  
    defocSp pf ω pL = hyp (erasex Z)
    defocSp pf ω (↑L N₁) = defocN pf (I ω) N₁
    defocSp pf ω (⊃L V₁ Sp₂) with ω
    ... | ≺*≡  = 
      subst ω 
        (⊃E (hyp Z) (WK-N.wkN (⊆to/wken* ω (⊆to/refl _)) (defocV pf V₁)))
        (WK-N.wkN wkex (defocSp pf ω Sp₂))
    ... | ≺*+ ω' = {! subst ω ? (WK-N.wkN wkex (defocSp pf ω Sp₂))!}

   -- open SEQUENT UWF dec≺

{-

   -- Equivalence of natural deduction and sequent calculus
   -- Things are set up such that we have to prove both at once
   equivP : W → Set
   equivP = λ w → 
      ((∀{Γ A} → Γ ⊢ A [ w ] → Γ ⇒ A [ w ]) 
      × (∀{Γ A} → Γ ⇒ A [ w ] → Γ ⊢ A [ w ]))

   -- Given the induction hypothesis, natural deduction implies sequent
   

   nd→seq' : (w : W) → ((w' : W) → w ≺+ w' → equivP w')
              → ∀{Γ A} → Γ ⊢ A [ w ] → Γ ⇒ A [ w ]
   nd→seq' w ih (hyp iN) = ident iN
   nd→seq' w ih (⊃I D) = ⊃R (nd→seq' w ih D)
   nd→seq' w ih (⊃E D D') = 
      cut (nd→seq' w ih D')
       (cut (wkS wken (nd→seq' w ih D))
        (⊃L ≺*≡ Z (ident (S Z)) (ident Z)))
   nd→seq' w ih (⊥E ≺*≡ D) = cut (nd→seq' w ih D) (⊥L ≺*≡ Z)
   nd→seq' w ih (⊥E (≺*+ ωh) D) = cut (fst (ih _ ωh) D) (⊥L (≺*+ ωh) Z)
   nd→seq' w ih (◇I ω D) = ◇R ω (fst (ih _ (≺+0 ω)) D)
   nd→seq' w ih (◇E ≺*≡ D D') = 
      cut (nd→seq' w ih D) 
       (◇L ≺*≡ Z λ ω D₀ → wkS wken 
        (nd→seq' w ih (D' ω (snd (ih _ (≺+0 ω)) (wkS (wkto ω) D₀)))))
   nd→seq' w ih (◇E (≺*+ ωh) D D') = 
      cut (fst (ih _ ωh) D) (◇L (≺*+ ωh) Z 
       λ ω D₀ → decut (fst (ih _ ωh) D) (nd→seq' w ih 
        (D' ω (snd (ih _ (≺+S' ωh ω)) (wkS (wkto ω) D₀)))))
   nd→seq' w ih (□I D) = □R (λ ω → fst (ih _ (≺+0 ω)) (D ω))
   nd→seq' w ih (□E ≺*≡ D D') =
      cut (nd→seq' w ih D) 
       (□L ≺*≡ Z (λ D₀ → wkS wken (nd→seq' w ih 
        (D' (λ ω → snd (ih _ (≺+0 ω)) (wkS (wkto ω) (D₀ ω)))))))
   nd→seq' w ih (□E (≺*+ ωh) D D') = 
     cut (fst (ih _ ωh) D) 
       (□L (≺*+ ωh) Z (λ D₀ → decut (fst (ih _ ωh) D) (nd→seq' w ih 
        (D' (λ ω → snd (ih _ (≺+S' ωh ω)) (wkS (wkto ω) (D₀ ω)))))))

   -- Given the induction hypothesis, sequent implies natural deduction
   seq→nd' : (w : W) → ((w' : W) → w ≺+ w' → equivP w')
              → ∀{Γ A} → Γ ⇒ A [ w ] → Γ ⊢ A [ w ]
   seq→nd' w ih (hyp iN) = hyp iN
   seq→nd' w ih (⊃R D) = ⊃I (seq→nd' w ih D)
   seq→nd' w ih (⊃L ≺*≡ iN D D') = 
      subst ≺*≡ (⊃E (hyp iN) (seq→nd' w ih D)) (seq→nd' w ih D')
   seq→nd' w ih (⊃L (≺*+ ωh) iN D D') = 
      subst (≺*+ ωh) (⊃E (hyp iN) (snd (ih _ ωh) D)) (seq→nd' w ih D')
   seq→nd' w ih (⊥L ωh iN) = ⊥E ωh (hyp iN) 
   seq→nd' w ih (◇R ω D) = ◇I ω (snd (ih _ (≺+0 ω)) D)
   seq→nd' w ih (◇L ωh iN D) = 
      ◇E ωh (hyp iN)
       (λ ω D₀ → seq→nd' w ih (D ω (fst (ih _ (≺*S' ωh ω)) D₀))) 
   seq→nd' w ih (□R D) = □I (λ ω → snd (ih _ (≺+0 ω)) (D ω))
   seq→nd' w ih (□L ωh iN D) = 
      □E ωh (hyp iN) 
       (λ D₀ → seq→nd' w ih (D (λ ω → fst (ih _ (≺*S' ωh ω)) (D₀ ω)))) 

   -- Therefore, both sequent calculus and natural deduction are equivalent
   nd⇆seq : (w : W) → 
      ((∀{Γ A} → Γ ⊢ A [ w ] → Γ ⇒ A [ w ]) 
      × (∀{Γ A} → Γ ⇒ A [ w ] → Γ ⊢ A [ w ]))
   nd⇆seq = 
      ind+ equivP (λ w ih → (λ D → nd→seq' _ ih D) , (λ D → seq→nd' _ ih D))

   nd→seq : ∀{Γ A w} → Γ ⊢ A [ w ] → Γ ⇒ A [ w ]
   nd→seq = fst (nd⇆seq _)

   seq→nd : ∀{Γ A w} → Γ ⇒ A [ w ] → Γ ⊢ A [ w ]
   seq→nd = snd (nd⇆seq _)

-}