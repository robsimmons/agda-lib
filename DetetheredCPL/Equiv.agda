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
  open CUT UWF
  open IDENTITY UWF

  eraseA : ∀{⁼} → Type ⁼ → UType
  eraseA {⁼} (a Q .⁼) = a Q -- ERROR!!!
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

  PdefocN : W → Set
  PdefocN wc = ∀{Γ Ω A}
    → wc ≺' Ω
    → Term [] Γ wc Ω (Reg A)
    → (eraseΩ Ω ++ eraseΓ Γ) ⊢ eraseA A [ wc ]

  record Pequiv (wc : W) : Set where
   field
    defocN : Unit -- PdefocN wc

  module EQUIV-LEM (wc : W) (ih : (wc' : W) → wc ≺+ wc' → Pequiv wc') where

    defocN : PdefocN wc


    defocN ω (L pf⁺ N₁) = {!!}
    defocN ω (↓L pf⁻ ωh x Sp) = {!!}
    defocN (I ω) ⊥L = ⊥E ω (hyp Z)
    defocN (I ω) (◇L N₁) = ◇E ω (hyp Z) 
      λ ω' D₀ → {! defocN · (N₁ ω' {!!}) !}
    defocN (I ω) (□L N₁) = □E ω (hyp Z) λ D₀ → {!!}
    defocN ω (↑R V₁) = {!!}
    defocN ω (⊃R N₁) = {!!}
  
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