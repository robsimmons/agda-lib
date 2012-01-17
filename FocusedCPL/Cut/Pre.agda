-- Constructive Provability Logic
-- Focused variant
-- Robert J. Simmons, Bernardo Toninho

-- Before the main cut proof
  -- Removing an assumption given evidence
  -- Ugly evidence 

open import Prelude hiding (⊥)
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import FocusedCPL.Core
open import FocusedCPL.Weakening
import FocusedCPL.Cut.Evidence
import FocusedCPL.Cut.IH

module FocusedCPL.Cut.Pre (UWF : UpwardsWellFounded) where
open TRANS-UWF UWF
open FocusedCPL.Cut.Evidence UWF
open FocusedCPL.Cut.IH UWF

module PRE-STEP 
  (dec≺ : (w w' : W) → Decidable (w ≺* w')) 
  (wc : W) (ih : (wc' : W) → wc ≺+ wc' → IH.P dec≺ wc') where
  open ILIST UWF
  open SEQUENT UWF
  open WEAKENING UWF
  open EVIDENCE dec≺
  open IH dec≺

  unwind' : ∀{Γ A C w w' b} 
    → wc ≺+ w
    → w ≺* w'
    → (Reg C) stable⁻
    → Atomic [] Γ w' A b
    → Spine [] Γ w' A w (Reg C)
    → Term [] Γ w · (Reg C)
  unwind' ω+ ω* pf (↓E x) Sp = ↓L pf ω* x Sp
  unwind' ω+ ω* pf (Cut N) Sp = P.subst⁻ (ih _ ω+) pf ω* N Sp
  unwind' ω+ ω* pf (⊃E R V) Sp = unwind' ω+ ω* pf R (⊃L V Sp)

  decutR : ∀{b b' Γ w w' A C}
    → wc ≺+ w
    → w ≺* w'
    → Atomic [] Γ w' (↑ A) b'
    → Atomic [] Γ w C b
    → Atomic [] ((A at w') :: Γ) w C b
  decutR ω+ ω* R (↓E x) = ↓E (S x)
  decutR ω+ ≺*≡ R (Cut N) = Cut (wkN <> (⊆to/wken (⊆to/refl _)) · N) 
  decutR ω+ (≺*+ ω) R (Cut N) = Cut (P.decutN (ih _ ω+) (N+ ω R) ·t N)
  decutR ω+ ≺*≡ R (⊃E R' V) = 
    ⊃E (decutR ω+ ≺*≡ R R') (wkV <> (⊆to/wken (⊆to/refl _)) V)
  decutR ω+ (≺*+ ω) R (⊃E R' V) = 
    ⊃E (decutR ω+ (≺*+ ω) R R') (P.decutV (ih _ ω+) (N+ ω R) V)

  carry-evidence : ∀{w w' Γ Γ' A}
    → wc ≺+ w'
    → w' ≺* w
    → Evidence Γ wc Γ' (A at w)
    → Atomic [] (Γ' ++ Γ) w (↑ A) True
  carry-evidence ω+ ω* (N⊀ ω) = abort (ω (≺+*trans ω+ ω*))
  carry-evidence ω+ ω* (N+ ω R) = subset R
  carry-evidence ω+ ω* (C⊀ ω edΓ) = 
    wkR (⊆to/wkenirrev (λ ω' → abort (ω (≺+*trans ω+ (≺*trans ω* ω'))))
          (⊆to/refl _)) (carry-evidence ω+ ω* edΓ)
  carry-evidence {w} ω+ ω* (C+ {wh} ω R edΓ) with dec≺ w wh
  ... | Inl ω' = decutR (≺+*trans ω+ ω*) ω' R (carry-evidence ω+ ω* edΓ) 
  ... | Inr ω' = 
    wkR (⊆to/wkenirrev ω' (⊆to/refl _)) (carry-evidence ω+ ω* edΓ) 

  re-cut-evidence : ∀{w w' Γ Γ' A C}
    → wc ≺+ w'
    → w' ≺* w
    → (Reg C) stable⁻
    → Evidence Γ wc Γ' (A at w)
    → Term [] (Γ' ++ A at w :: Γ) w' · (Reg C)
    → Term [] (Γ' ++ Γ) w' · (Reg C)
  re-cut-evidence {Γ' = Γ'} ω+ ω* pf⁻ ed N = 
    unwind' ω+ ω* {!!} (carry-evidence ω+ ω* ed) 
      (↑L (L {!!} (wkN <> (⊆to/append-swap Γ' [ _ ]) · N))) 
   -- carry-evidence ω+ ω* ed

  re-cut-evidence' : ∀{w w' Γ Γ' A B b wh C}
    → EvidenceΩ (Γ' ++ Γ) wc (I B wh) b
    → wh ≺ w'
    → (Reg C) stable⁻
    → Evidence Γ wc Γ' (A at w)
    → Term [] (Γ' ++ A at w :: Γ) w' · (Reg C)
    → Term [] (Γ' ++ Γ) w' · (Reg C)
  re-cut-evidence' {w} {w'} ed ω pf⁻ edΓ N with dec≺ w' w
  re-cut-evidence' {Γ' = Γ'} ed ω pf⁻ edΓ N | Inr ω' = 
    wkN <> (⊆to/append-congr Γ' (⊆to/stenirrev ω' (⊆to/refl _))) · N
  re-cut-evidence' I≡ ω pf⁻ edΓ N | Inl ω' =
    re-cut-evidence (≺+0 ω) ω' pf⁻ edΓ N
  re-cut-evidence' (I+ ω'' _) ω pf⁻ edΓ N | Inl ω' =
    re-cut-evidence (≺+S' ω'' ω) ω' pf⁻ edΓ N

  decutV : PdecutV wc
  decutN : PdecutN wc
  decutSp : PdecutSp wc

  decutV {Γ'} edΓ (pR x) = pR (LIST.SET.sub-append-congr Γ' LIST.SET.sub-wken x)
  decutV edΓ (↓R N₁) = ↓R (decutN edΓ ·t N₁)
  decutV edΓ (◇R ω N₁) = ◇R ω (P.decutN (ih _ (≺+0 ω)) (ed≺ ω edΓ) ·t N₁)
  decutV edΓ (□R N₁) = □R λ ω → P.decutN (ih _ (≺+0 ω)) (ed≺ ω edΓ) ·t (N₁ ω)

  decutN edΓ I≡ (L pf⁺ N₁) = L pf⁺ (decutN (C⊀ (nrefl+ _ _ refl) edΓ) ·t N₁)
  decutN edΓ (I+ ω R) (L pf⁺ N₁) = L pf⁺ (decutN (C+ ω R edΓ) ·t N₁)
  decutN {Γ'} edΓ ed (↓L pf⁻ ωh x Sp) = 
    ↓L pf⁻ ωh (LIST.SET.sub-append-congr Γ' LIST.SET.sub-wken x) 
      (decutSp edΓ (varE {b = True} x ωh) Sp)
  decutN edΓ ed ⊥L = ⊥L
  decutN edΓ ed (◇L N₁) = 
    ◇L λ ω N₀ → decutN edΓ ·t (N₁ ω (re-cut-evidence' ed ω {!!} edΓ N₀))
  decutN edΓ ed (□L N₁) = 
    □L λ N₀ → decutN edΓ ·t (N₁ λ ω → (re-cut-evidence' ed ω {!!} edΓ (N₀ ω)))
  decutN edΓ ed (↑R V₁) = ↑R (decutV edΓ V₁)
  decutN edΓ ed (⊃R N₁) = ⊃R (decutN {b = True} edΓ I≡ N₁) 

  decutSp edΓ ed pL = pL
  decutSp edΓ ed (↑L N₁) = ↑L (decutN edΓ (atmE ed) N₁)
  decutSp edΓ E≡ (⊃L V₁ Sp₂) = 
    ⊃L (decutV edΓ V₁) (decutSp {b = True} edΓ (appE E≡ V₁) Sp₂)
  decutSp edΓ (E+ ω R) (⊃L V₁ Sp₂) = 
    ⊃L (P.decutV (ih _ ω) (ed≺+ ω edΓ) V₁) 
      (decutSp edΓ (appE (E+ ω R) V₁) Sp₂)

  -- Ugly evidence-managing lemmas

  weaken-with-evidence-r : ∀{w wh Γ C b} {B : Type ⁺}
    → wc ≺* w
    → EvidenceΩ Γ wc (I B wh) b
    → Term [] Γ w · (Reg C)
    → Term [] ((B at wh) :: Γ) w · (Reg C)
  weaken-with-evidence-r {w} {wh} ω ed N with dec≺ w wh 
  weaken-with-evidence-r ω ed N | Inr ωh =
    wkN <> (⊆to/wkenirrev ωh (⊆to/refl _)) · N
  weaken-with-evidence-r ω ed N | Inl ≺*≡ = 
    wkN <> (⊆to/wken (⊆to/refl _)) · N
  weaken-with-evidence-r ω I≡ N | Inl (≺*+ ωh) = abort (≺+⊀ ωh ω)
  weaken-with-evidence-r ≺*≡ (I+ ωq R) N | Inl (≺*+ ωh) = 
    decutN (N+ ωh R) ·t N
  weaken-with-evidence-r (≺*+ ω) (I+ ωq R) N | Inl (≺*+ ωh) = 
    P.decutN (ih _ ω) (N+ ωh R) ·t N

  weaken-with-evidence-l : ∀{w wh C A B Γ}
    → B stable⁺
    → wc ≺* w
    → EvidenceΩ Γ wc (I B wh) False
    → Term [] ((B at wh) :: Γ) w · (Reg (↑ A))
    → Term [] Γ wc (I A w) (Reg C)
    → Term [] ((B at wh) :: Γ) wc (I A w) (Reg C)
  weaken-with-evidence-l pf ω I≡ N₁ N' = 
    wkN <> (⊆to/wken (⊆to/refl _)) (I ω) N'
  weaken-with-evidence-l pf ≺*≡ (I+ ω' R) N₁ N' = 
    decutN {b = False} (N+ ω' R) I≡ N'
  weaken-with-evidence-l {w} {wh} pf (≺*+ ω) (I+ ω' R) N₁ N' with dec≺ w wh
  ... | Inl ω'' = 
    decutN (N+ ω' R) 
      (I+ ω (Cut (unwind <> ω'' R (↑L (L pf N₁))))) N' 
  ... | Inr ω'' = 
    decutN (N+ ω' R) 
      (I+ ω (Cut (wkN <> (⊆to/stenirrev ω'' (⊆to/refl _)) · N₁))) N'

  decut : ∀{w w' Γ A B C b wh}
    (Γ' : MCtx)
    → EvidenceΩ (Γ' ++ Γ) wc (I C wh) b
    → wh ≺ w
    → Term [] (Γ' ++ Γ) w' · (Reg A)
    → Term [] (Γ' ++ Γ) w · (Reg B)
    → Term [] (Γ' ++ (↓ A at w') :: Γ) w · (Reg B)
  decut {w} {w'} Γ' ed ω N N₀ with evidenceΩ≺ ed | dec≺ w w'
  decut Γ' ed ω N N₀ | _ | Inr ω' = 
    wkN <> (⊆to/append-congr Γ' (⊆to/wkenirrev ω' (⊆to/refl _))) · N₀
  decut Γ' ed ω N N₀ | _ | Inl ≺*≡ = 
    wkN <> (⊆to/append-congr Γ' (⊆to/wken (⊆to/refl _))) · N₀
  decut Γ' ed ω N N₀ | (I ωed) | Inl (≺*+ ω') = 
    wkN <> (⊆to/append-swap [ _ ] Γ') ·
      (P.decutN (ih _ (≺*S' ωed ω)) (N+ ω' (Cut (↑R (↓R N)))) ·t N₀)
  
  -- Decidability-endowed versions of regular cuts

  ih-rsubstN : ∀{wc' w Γ A C} 
      → wc ≺+ wc'
      → (Γ' : MCtx)
      → Term [] (Γ' ++ Γ) w · (Reg A)
      → Term [] (Γ' ++ ↓ A at w :: Γ) wc' · (Reg C)
      → Term [] (Γ' ++ Γ) wc' · (Reg C)
  ih-rsubstN {wc'} {w} ω Γ' N M with dec≺ wc' w
  ... | Inl ω' = P.rsubstN (ih _ ω) Γ' ω' N M ·t
  ... | Inr ω' = 
    wkN <> (⊆to/append-congr Γ' (⊆to/stenirrev ω' (⊆to/refl _))) · M

  ih-rsubstV : ∀{wc' w Γ A C}
      → wc ≺+ wc'
      → (Γ' : MCtx)
      → Term [] (Γ' ++ Γ) w · (Reg A)
      → Value [] (Γ' ++ ↓ A at w :: Γ) wc' C
      → Value [] (Γ' ++ Γ) wc' C
  ih-rsubstV {wc'} {w} ω Γ' N V with dec≺ wc' w
  ... | Inl ω' = P.rsubstV (ih _ ω) Γ' ω' N V
  ... | Inr ω' = 
    wkV <> (⊆to/append-congr Γ' (⊆to/stenirrev ω' (⊆to/refl _))) V
