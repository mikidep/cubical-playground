open import CubicalPlayground.Prelude

open import Cubical.Foundations.Function using (idfun; _∘_; ∘-assoc)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
open import Cubical.Foundations.Path using (compPath→Square; cong′)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Functions.FunExtEquiv using (funExtDep; funExtDep⁻)
open import Cubical.HITs.FiniteMultiset as FMSet using (FMSet; []; _∷_)
open import Cubical.HITs.SetTruncation as SetTrunc
  using (∥_∥₂; ∣_∣₂; isSetSetTrunc)

open import CubicalPlayground.LoopyChain.Base using (LoopyChain; AdjLoop)
open import CubicalPlayground.Endofunctor using (Endofunctor; iterate; iterate-endo)
open import CubicalPlayground.Colimit as Colim
  using (Cocone; leg; com; colim; colim-leg; colim-com; DepCocone; com-∘)

module CubicalPlayground.Bag where

data LoopIdx : ℕ → Type where
  swapIdx : ∀ n → LoopIdx (2 + n)
  F<$>idx : ∀ n → LoopIdx (n) → LoopIdx (suc n)

open LoopyChain

module _ (A : Type) where
  data ListF (X : Type) : Type where
    nil : ListF X
    cons : (a : A) (x : X) → ListF X

  ListF-map : {X Y : Type} → (X → Y) → ListF X → ListF Y
  ListF-map f nil = nil
  ListF-map f (cons a x) = cons a (f x)

  open Endofunctor

  ListEndo : Endofunctor
  ListEndo .F = ListF
  ListEndo <$> f = ListF-map f
  ListEndo .hom-id = funExt hom
    where
    hom : (x : ListF _) →
        (ListEndo <$> idfun _) x ≡ idfun (ListF _) x
    hom nil = refl
    hom (cons a x) = refl
  ListEndo .hom-∘ f g = funExt hom
    where
    hom : (x : ListF _)
      → (ListEndo <$> g ∘ ListEndo <$> f) x ≡ (ListEndo <$> (g ∘ f)) x
    hom nil = refl
    hom (cons a x) = refl

  ListEndo^ : ℕ → Endofunctor
  ListEndo^ = iterate-endo ListEndo

  bagChain-Ob : ℕ → Type
  bagChain-Ob n = iterate (ListEndo .F) n ⊥

  swap : (n : ℕ) → bagChain-Ob (2 + n) → bagChain-Ob (2 + n)
  swap _ (cons a₁ (cons a₂ l)) = (cons a₂ (cons a₁ l))
  swap _ l = l

  bagChain : LoopyChain LoopIdx
  bagChain .Ob = bagChain-Ob
  bagChain .ι = bagChain-ι
    where
    ! : ⊥ → ListEndo .F ⊥
    ! ()
    bagChain-ι : (n : ℕ) → iterate (ListEndo .F) n ⊥ → ListEndo .F (iterate (ListEndo .F) n ⊥)
    bagChain-ι zero = !
    bagChain-ι (suc n) = ListEndo <$> bagChain-ι n
  bagChain .loop = bagChain-loop
    where
    bagChain-loop : ∀ n → LoopIdx n → bagChain-Ob n → bagChain-Ob n
    bagChain-loop .(2 + n) (swapIdx n) = swap n
    bagChain-loop .(suc n) (F<$>idx n idx) = ListEndo <$> bagChain-loop n idx

  bag-colim = colim (asDiag bagChain)

  bag-nil : bag-colim
  bag-nil = colim-leg 1 nil

  open AdjLoop using (next; loopIdx)
  bag-cons-cocone : A → Cocone _ (asDiag bagChain) bag-colim
  bag-cons-cocone a .leg n = cons a » colim-leg (suc n)
  bag-cons-cocone a .com {j = .n} (next n) =
      bagChain .ι n » cons a » l (suc (suc n))
    ≡⟨⟩
      cons a » bagChain .ι (suc n) » l (suc (suc n))
    ≡⟨ cong (cons a »_) (colim-com (next (suc n))) ⟩∎
      cons a » l (suc n)
    ∎
    where
    l = colim-leg
  bag-cons-cocone a .com {j = .n} (loopIdx n idx) =
      bagChain .loop n idx » cons a » l (suc n)
    ≡⟨⟩
      cons a » bagChain .loop (suc n) (F<$>idx n idx) » l (suc n)
    ≡⟨ cong (cons a »_) (colim-com (loopIdx (suc n) (F<$>idx n idx))) ⟩∎
      cons a » l (suc n)
    ∎
    where
    l = colim-leg
    top-comm : LoopIdx n
              → bagChain .loop n idx » cons a
                ≡ cons a » bagChain .loop (suc n) (F<$>idx n idx)
    top-comm _ = refl
  bag-cons : A → bag-colim → bag-colim
  bag-cons a = Colim.rec (bag-cons-cocone a)

--   _++_ : bag-colim → bag-colim → bag-colim
--   b₁ ++ b₂ = Colim.rec cocone b₁
--     where
--     cocone-leg : (n : ℕ) → bagChain-Ob n → bag-colim
--     cocone-leg (suc n) nil = b₂
--     cocone-leg (suc n) (cons a l) = bag-cons a (cocone-leg n l)
--     open AdjLoop
--     cocone : Cocone (ℓ-suc (ℓ-suc ℓ-zero)) (asDiag bagChain) bag-colim
--     cocone .leg = cocone-leg
--     cocone .com {j = n} (next .n) = cocone-com-next n
--       where
--       cocone-com-next : ∀ n
--         →  bagChain .ι n » cocone .leg (suc n) ≡ cocone .leg n
--       cocone-com-next zero = funExt λ ()
--       cocone-com-next (suc n) = funExt hom
--         where
--         hom : ∀ l
--           → bagChain .ι (suc n) » cocone-leg (suc (suc n)) $ l ≡ cocone-leg (suc n) l
--         hom nil = refl
--         hom (cons a l) = path ≡$ l
--           where
--           path : cons a » bagChain .ι (suc n) » cocone-leg (suc (suc n)) ≡ cons a » cocone-leg (suc n)
--           path =
--               cons a » bagChain .ι (suc n) » cocone-leg (suc (suc n))
--             ≡⟨ cong (_» cocone-leg (suc (suc n))) (sym $ ι-cons-comm n a) ⟩
--               bagChain .ι n » cons a » cocone-leg (suc (suc n))
--             ≡⟨⟩
--               bagChain .ι n » cocone-leg (suc n) » Colim.rec (bag-cons-cocone a)
--             ≡⟨ cong (_» Colim.rec (bag-cons-cocone a)) (cocone-com-next n) ⟩∎
--               cocone-leg n » Colim.rec (bag-cons-cocone a) ∎
--             ≡⟨⟩∎
--               cons a » cocone-leg (suc n)
--     cocone .com {j = n} (loopIdx .n idx) = cocone-com-loop n idx
--       where
--       cocone-com-loop : ∀ n (idx : LoopIdx n)
--         → cocone-leg n ∘ bagChain .loop n idx ≡ cocone-leg n
--       cocone-com-loop .(2 + n) (swapIdx n) = funExt hom
--         where
--         hom : ∀ l
--           → (cocone-leg (suc (suc n)) ∘ swap n) l ≡ cocone-leg (suc (suc n)) l
--         hom nil = refl
--         hom (cons a nil) = refl
--         hom (cons a (cons a₁ l)) = {!   !}
--       cocone-com-loop .(suc n) (F<$>idx n idx) = {!   !}

  cong■ : ∀ {ℓ ℓ'}
    {A : Type ℓ} {B : Type ℓ'}
    {tl tr bl br : A}
    {te : tl ≡ tr}
    {be : bl ≡ br}
    {le : tl ≡ bl}
    {re : tr ≡ br}
    (f : A → B)
    → Square te be le re
    → Square (cong f te) (cong f be) (cong f le) (cong f re)
  cong■ f sq i j = f $ sq i j

  comp-com : ∀ {ℓ ℓ'} {A B C : Type ℓ} {V : Type ℓ'}
    {f : A → B}
    {g : B → C}
    {lA : A → V}
    {lB : B → V}
    {lC : C → V}
    → f » lB ≡ lA
    → g » lC ≡ lB
    → f » g » lC ≡ lA
  comp-com {f = f} com-f com-g = cong (f »_) com-g ∙ com-f

  lemma : ∀ {ℓ ℓ'} {A B B' C : Type ℓ} {V : Type ℓ'}
    {f  : A  → B }
    {g  : B  → C }
    {f' : A  → B'}
    {g' : B' → C }
    {lA  : A  → V }
    {lB  : B  → V }
    {lB' : B' → V }
    {lC  : C  → V }
    {com-f  : f  » lB  ≡ lA }
    {com-g  : g  » lC  ≡ lB }
    {com-f' : f' » lB' ≡ lA }
    {com-g' : g' » lC  ≡ lB'}
    {2-cell : f » g ≡ f' » g'}
    → (comp-com {lC = lC} com-f com-g ≡[ 2-cell , (λ f → f » lC ≡ lA) ] comp-com {lC = lC} com-f' com-g')
      ≡ Square 
        (comp-com {lC = lC} com-f  com-g ) -- cong (f  »_) com-g  ∙ com-f
        (comp-com {lC = lC} com-f' com-g') -- cong (f' »_) com-g' ∙ com-f'
        (cong (_» lC) 2-cell) 
        refl
  lemma = refl

  sq-weird-funExt : ∀ {ℓ ℓ'}
    {A : Type ℓ} {B : Type ℓ'}
    {tl tr bl br : A → B}
    {te : tl ≡ tr}
    {be : bl ≡ br}
    {le : tl ≡ bl}
    {re : tr ≡ br}
    → PathP (λ i → (x : A) → le i x ≡ re i x) (te ≡$_) (be ≡$_)
    → (Square te be le re)
  sq-weird-funExt what i j x = what i x j

  sq-weird-funExt⁻ : ∀ {ℓ ℓ'}
    {A : Type ℓ} {B : Type ℓ'}
    {tl tr bl br : A → B}
    {te : tl ≡ tr}
    {be : bl ≡ br}
    {le : tl ≡ bl}
    {re : tr ≡ br}
    → Square te be le re
    → PathP (λ i → (x : A) → le i x ≡ re i x) (te ≡$_) (be ≡$_)
  sq-weird-funExt⁻ sq i x j = sq i j x

  sq-funExt : ∀ {ℓ ℓ'}
    {A : Type ℓ} {B : Type ℓ'}
    {tl tr bl br : A → B}
    {teh : ∀ x → tl x ≡ tr x}
    {beh : ∀ x → bl x ≡ br x}
    {leh : ∀ x → tl x ≡ bl x}
    {reh : ∀ x → tr x ≡ br x}
    → (∀ x → Square (teh x) (beh x) (leh x) (reh x))
    → Square (funExt teh) (funExt beh) (funExt leh) (funExt reh)
  sq-funExt sqh i j x = sqh x i j

  open AdjLoop
  bag-eq : ∀ a₁ a₂ b → bag-cons a₁ (bag-cons a₂ b) ≡ bag-cons a₂ (bag-cons a₁ b)
  bag-eq a₁ a₂ = Colim.elim dep-cocone
    where
    open DepCocone
    dep-cocone :
      DepCocone
        _
        (asDiag bagChain)
        _
        (λ b → bag-cons a₁ (bag-cons a₂ b) ≡ bag-cons a₂ (bag-cons a₁ b))
    dep-cocone .leg n l = colim-com (loopIdx (suc (suc n)) (swapIdx n)) ≡$ (cons a₂ (cons a₁ l))
    
    dep-cocone .com {j = n} (next n) = sq-weird-funExt⁻ sq
      where    
      ι' = bagChain .ι
      l = colim-leg {F = asDiag bagChain}
      tl tr bl br : bagChain .Ob n → colim (asDiag bagChain)
      tl = cons a₁ » cons a₂ » ι' (2 + n) » swap (suc n) » l (3 + n)
      tr = cons a₁ » cons a₂ » ι' (2 + n) » l (3 + n)
      bl = cons a₁ » cons a₂ » swap n » l (2 + n)
      br = cons a₁ » cons a₂ » l (2 + n)
      te : tl ≡ tr
      te = cong (cons a₁ » cons a₂ » ι' (2 + n) »_) $ colim-com (loopIdx _ (swapIdx (1 + n)))
      be : bl ≡ br
      be = cong (cons a₁ » cons a₂ »_) $ colim-com (loopIdx (2 + n) (swapIdx n))
      le : tl ≡ bl
      le = cong (cons a₁ » cons a₂ » swap n »_) $ colim-com (next (2 + n))
      re : tr ≡ br
      re = cong (cons a₁ » cons a₂ »_) $ colim-com (next (2 + n))
      2-cell : ∀ n → swap n » ι' (2 + n) ≡ ι' (2 + n) » swap (1 + n)
      2-cell n = funExt (hom n)
        where
        hom : ∀ n l → swap n » ι' (2 + n) $ l ≡ ι' (2 + n) » swap (1 + n) $ l
        hom n nil = refl
        hom n (cons a nil) = refl
        hom n (cons a₁ (cons a₂ l)) = refl
      com-com-sq : Square
        (com-∘ (loopIdx (2 + n) (swapIdx n)) (next (2 + n)))
        (com-∘ (next (2 + n)) (loopIdx (3 + n) (swapIdx (1 + n))))
        (cong (_» l (3 + n)) $ 2-cell n) 
        refl
      com-com-sq = {!   !}
      sq : Square te be le re
      sq = compPath→Square $ cong■ (cons a₁ » cons a₂ »_) com-com-sq
    
    dep-cocone .com {j = .(2 + n)} (loopIdx .(2 + n) (swapIdx n)) = sq-weird-funExt⁻ sq
      where
      l = colim-leg
      loop' : ∀ {n} → _
      loop' {n} = bagChain .loop n
      F$_ : ∀ {n} → _ → _
      F$_ {n} = F<$>idx n
      tl tr bl br : bagChain .Ob (2 + n) → colim (asDiag bagChain)
      tl = cons a₁ » cons a₂ » loop' (F$ F$ swapIdx n) » swap (2 + n) » l (4 + n)
      tr = cons a₁ » cons a₂ » loop' (F$ F$ swapIdx n) » l (4 + n)
      bl = cons a₁ » cons a₂ » swap (2 + n) » l (4 + n)
      br = cons a₁ » cons a₂ » l (4 + n)
      te : tl ≡ tr
      te = cong (cons a₁ » cons a₂ » loop' (F$ F$ swapIdx n) »_) $ colim-com (loopIdx _ (swapIdx (2 + n)))
      be : bl ≡ br
      be = cong (cons a₁ » cons a₂ »_) $ colim-com (loopIdx _ (swapIdx (2 + n)))
      le : tl ≡ bl
      le = cong (cons a₁ » cons a₂ » swap (2 + n) »_) $ colim-com (loopIdx _ (F$ F$ swapIdx n))
      re : tr ≡ br
      re = cong (cons a₁ » cons a₂ »_) $ colim-com (loopIdx _ (F$ F$ swapIdx n))
      2-cell : ∀ n → swap (2 + n) » loop' (F$ F$ swapIdx n) ≡ loop' (F$ F$ swapIdx n) » swap (2 + n)
      2-cell n = funExt hom
        where
        hom : ∀ l →
            (swap (2 + n) » loop' (F$ F$ swapIdx n)) l
          ≡
            (loop' (F$ F$ swapIdx n) » swap (2 + n)) l
        hom nil = refl
        hom (cons a nil) = refl
        hom (cons a (cons a₁ nil)) = refl
        hom (cons a (cons a₁ (cons a₂ nil))) = refl
        hom (cons a (cons a₁ (cons a₂ (cons a₃ _)))) = refl
      com-com-sq : Square
        (com-∘ (loopIdx _ (swapIdx (2 + n))) (loopIdx _ (F$ (F$ swapIdx n))))
        (com-∘ (loopIdx _ (F$ (F$ swapIdx n))) (loopIdx _ (swapIdx (2 + n))))
        (cong (_» l (4 + n)) $ 2-cell n)
        refl
      com-com-sq = {!   !}
      cong-com-com-te = (cong (cons a₁ » cons a₂ »_) $ com-∘ (loopIdx _ (swapIdx (2 + n))) (loopIdx _ (F$ (F$ swapIdx n))))
      cong-com-com-be = (cong (cons a₁ » cons a₂ »_) $ com-∘ (loopIdx _ (F$ (F$ swapIdx n))) (loopIdx _ (swapIdx (2 + n))))
      cong-com-com-le = (cong (cons a₁ » cons a₂ »_) $ cong (_» l (4 + n)) $ 2-cell n)
      cong-com-com-sq : Square
        cong-com-com-te
        cong-com-com-be
        cong-com-com-le
        refl
      cong-com-com-sq = cong■ (cons a₁ » cons a₂ »_) com-com-sq
      cong-com-com-le≡refl : cong-com-com-le ≡ refl
      cong-com-com-le≡refl i j nil = colim-leg (4 + n) (cons a₁ (cons a₂ nil))
      cong-com-com-le≡refl i j (cons a nil) = colim-leg (4 + n) (cons a₁ (cons a₂ (cons a nil)))
      cong-com-com-le≡refl i j (cons a (cons a' x)) = colim-leg (4 + n) (cons a₁ (cons a₂ (cons a' (cons a x))))
      le-refl-sq : Square
        cong-com-com-te
        cong-com-com-be
        refl
        refl
      le-refl-sq = transport
        (cong (λ e → Square
          cong-com-com-te
          cong-com-com-be
          e
          refl) cong-com-com-le≡refl)
        cong-com-com-sq
      sq : Square te be le re
      sq = compPath→Square le-refl-sq
    
    dep-cocone .com {j = .(suc n)} (loopIdx .(suc n) (F<$>idx n idx)) = sq-weird-funExt⁻ sq
      where
      l = colim-leg
      loop' : ∀ {n} → _
      loop' {n} = bagChain .loop n
      F$_ : ∀ {n} → _ → _
      F$_ {n} = F<$>idx n
      tl = cons a₁ » cons a₂ » loop' (F$ F$ F$ idx) » swap (1 + n) » l (3 + n)
      tr = cons a₁ » cons a₂ » loop' (F$ F$ F$ idx) » l (3 + n)
      bl = cons a₁ » cons a₂ » swap (1 + n) » l (3 + n)
      br = cons a₁ » cons a₂ » l (3 + n)
      te : tl ≡ tr
      te = cong (cons a₁ » cons a₂ »_)
          $ cong (loop' (F$ F$ F$ idx) »_) $ colim-com (loopIdx _ (swapIdx (1 + n)))
      be : bl ≡ br
      be = cong (cons a₁ » cons a₂ »_)
          $ colim-com (loopIdx _ (swapIdx (1 + n)))
      le : tl ≡ bl
      le = cong (cons a₁ » cons a₂ »_)
          $ cong (swap (1 + n) »_) $ colim-com (loopIdx _ (F$ F$ F$ idx))
      re : tr ≡ br
      re = cong (cons a₁ » cons a₂ »_)
          $ colim-com (loopIdx _ (F$ F$ F$ idx))
      2-cell : ∀ n idx
        → swap (1 + n) » loop' (F$ F$ F$ idx)
          ≡ loop' {n = 3 + n} (F$ F$ F$ idx) » swap (1 + n)
      2-cell _ _ = funExt hom
        where
        hom : _
        hom nil = refl
        hom (cons a nil) = refl
        hom (cons a (cons a₁ nil)) = refl
        hom (cons a (cons a₁ (cons a₂ _))) = refl
      com-com-le = cong (_» l (3 + n)) $ 2-cell n idx
      com-com-sq : Square
        (com-∘ (loopIdx _ $ swapIdx (1 + n)) (loopIdx _ $ F$ F$ F$ idx))
        (com-∘ (loopIdx _ $ F$ F$ F$ idx) (loopIdx _ $ swapIdx (1 + n)))
        com-com-le
        refl
      com-com-sq = {!   !}
      cong-com-com-te = cong (cons a₁ » cons a₂ »_) $ com-∘ (loopIdx _ $ swapIdx (1 + n)) (loopIdx _ $ F$ F$ F$ idx)
      cong-com-com-be = cong (cons a₁ » cons a₂ »_) $ com-∘ (loopIdx _ $ F$ F$ F$ idx) (loopIdx _ $ swapIdx (1 + n))
      cong-com-com-le = cong (cons a₁ » cons a₂ »_) $ cong (_» l (3 + n)) $ 2-cell n idx
      cong-com-com-sq : Square
        cong-com-com-te
        cong-com-com-be
        cong-com-com-le
        refl
      cong-com-com-sq = cong■ {le = com-com-le} (cons a₁ » cons a₂ »_) com-com-sq
      cong-com-com-le≡refl : cong-com-com-le ≡ refl
      cong-com-com-le≡refl i j nil = colim-leg (3 + n) (cons a₁ (cons a₂ nil))
      cong-com-com-le≡refl i j (cons a₃ l) = colim-leg (3 + n) (cons a₁ (cons a₂ (cons a₃ (loop' idx l))))
      le-refl-sq : Square
        cong-com-com-te
        cong-com-com-be
        refl
        refl
      le-refl-sq = transport
        (cong (λ e → Square
          cong-com-com-te
          cong-com-com-be
          e
          refl) cong-com-com-le≡refl)
        cong-com-com-sq
      sq : Square te be le re
      sq = compPath→Square le-refl-sq

  SetTrunc-ElimProp : ∀ {ℓ ℓ'} {A : Type ℓ} {P : ∥ A ∥₂ → Type ℓ'}
    → (∀ xt → isProp (P xt))
    → (∀ x → P ∣ x ∣₂)
    → ∀ xt → P xt
  SetTrunc-ElimProp isPropP f = SetTrunc.elim (λ xt → isProp→isSet (isPropP xt)) f

  trunc-comp-lemma : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f g : ∥ A ∥₂ → B)
    → isSet B
    → ∣_∣₂ » f ≡ ∣_∣₂ » g
    → f ≡ g
  trunc-comp-lemma {A = A} f g isSetB path = funExt hom
    where
    hom : (x : ∥ A ∥₂) → f x ≡ g x
    hom = SetTrunc-ElimProp (λ _ → (isSetB _ _)) (path ≡$_)

  trunc-colim = ∥ bag-colim ∥₂

  trunc-cons : A → trunc-colim → trunc-colim
  trunc-cons a = SetTrunc.rec
    isSetSetTrunc
    (bag-cons a » ∣_∣₂)

  trunc-eq : ∀ a₁ a₂ tb → trunc-cons a₁ (trunc-cons a₂ tb) ≡ trunc-cons a₂ (trunc-cons a₁ tb)
  trunc-eq a₁ a₂ = trunc-comp-lemma
    (trunc-cons a₁ ∘ trunc-cons a₂)
    (trunc-cons a₂ ∘ trunc-cons a₁)
    (isSetSetTrunc)
    (funExt $ Colim.elim dep-cocone) ≡$_
      where
      open DepCocone
      dep-cocone : DepCocone _  (asDiag bagChain) _ _
      dep-cocone .leg n l =
        cong ∣_∣₂ (colim-com (loopIdx (suc (suc n)) (swapIdx n)) ≡$ (cons a₂ (cons a₁ l)))
      dep-cocone .com f = funExtDep (λ p → isProp→PathP (λ i → isSetSetTrunc _ _) _ _)

  FMSet≃trunc-colim : FMSet A ≃ trunc-colim
  FMSet≃trunc-colim = isoToEquiv iso
    where
    iso-inv-cocone-leg : ∀ n → iterate (ListEndo .F) n ⊥ → FMSet A
    iso-inv-cocone-leg zero = λ ()
    iso-inv-cocone-leg (suc n) nil = []
    iso-inv-cocone-leg (suc n) (cons a l) = a ∷ iso-inv-cocone-leg n l
    iso-inv-cocone : Cocone _ (asDiag bagChain) (FMSet A)
    iso-inv-cocone .leg = iso-inv-cocone-leg
    iso-inv-cocone .com {j = n} (next .n) = cocone-com-ι n
      where
      cocone-com-ι : ∀ n → bagChain .ι n » iso-inv-cocone-leg (suc n) ≡ iso-inv-cocone-leg n
      cocone-com-ι zero = funExt λ ()
      cocone-com-ι (suc n) = funExt hom
        where
        hom : ∀ l → _
        hom nil = refl
        hom (cons a x) = cong (a ∷_) (cocone-com-ι n ≡$ x)
    iso-inv-cocone .com {j = n} (loopIdx .n idx) = cocone-com-loop n idx
      where
      cocone-com-loop : ∀ n idx → bagChain .loop n idx » iso-inv-cocone-leg n ≡ iso-inv-cocone-leg n
      cocone-com-loop .(2 + n) (swapIdx n) = funExt hom
        where
        hom : _
        hom nil = refl
        hom (cons a nil) = refl
        hom (cons a₁ (cons a₂ l)) = FMSet.comm a₂ a₁ (iso-inv-cocone-leg n l)
      cocone-com-loop .(suc n) (F<$>idx n idx) = funExt hom
        where
        hom : _
        hom nil = refl
        hom (cons a x) = cong (a ∷_) (cocone-com-loop n idx ≡$ x)
    open Iso
    iso : Iso (FMSet A) trunc-colim
    iso .fun = FMSet.Rec.f
      isSetSetTrunc ∣ bag-nil ∣₂ trunc-cons trunc-eq
    iso .inv = SetTrunc.rec FMSet.trunc (Colim.rec iso-inv-cocone)
    iso .rightInv b =
      trunc-comp-lemma
        (iso .fun ∘ iso .inv)
        (idfun _)
        isSetSetTrunc
        (funExt $ Colim.elim depCocone) ≡$ b
      where
      depCocone-leg : ∀ n l → colim-leg n » ∣_∣₂ » iso .inv » iso .fun $ l ≡ colim-leg n » ∣_∣₂ $ l
      depCocone-leg zero = λ ()
      depCocone-leg (suc n) nil = depCocone-leg-nil n
        where
        depCocone-leg-nil : ∀ n → _
        depCocone-leg-nil zero = refl      
        depCocone-leg-nil (suc n) =
            ∣ colim-leg 1 nil ∣₂
          ≡⟨ depCocone-leg-nil n ⟩
            ∣ colim-leg (suc n) $ nil ∣₂
          ≡⟨ cong ((_$ nil) » ∣_∣₂) $ sym $ colim-com (next (suc n)) ⟩∎
            ∣ bagChain .ι (suc n) » colim-leg (suc (suc n)) $ nil ∣₂ ∎
          ≡⟨⟩∎
            ∣ colim-leg (suc (suc n)) nil ∣₂
      depCocone-leg (suc n) (cons a l) =
          cons a » colim-leg (suc n) » ∣_∣₂ » iso .inv » iso .fun $ l
        ≡⟨⟩
          colim-leg n » ∣_∣₂ » iso .inv » iso .fun » trunc-cons a $ l
        ≡⟨ cong (trunc-cons a) (depCocone-leg n l) ⟩∎
          colim-leg n » ∣_∣₂ » trunc-cons a $ l ∎
        ≡⟨⟩∎
          cons a » colim-leg (suc n) » ∣_∣₂ $ l
      open DepCocone
      depCocone : DepCocone _ (asDiag bagChain) _ _
      depCocone .leg = depCocone-leg
      depCocone .com _ = funExt λ x → isProp→PathP (λ i → isSetSetTrunc _ _) _ _
    iso .leftInv fms = FMSet.ElimProp.f
      (λ {fms} → FMSet.trunc (iso .fun » iso .inv $ fms) fms)
      []*
      _∷_*
      fms
      where
      []* : iso .fun » iso .inv $ [] ≡ []
      []* = refl
      _∷_* : _
      _∷_* a {xs} IHxs =
          (a ∷_) » iso .fun » iso .inv $ xs
        ≡⟨⟩
          iso .fun » trunc-cons a » iso .inv $ xs
        ≡⟨⟩
          iso .fun » trunc-cons a » iso .inv $ xs
        ≡⟨ cong (λ f → iso .fun » f $ xs) p ⟩
          iso .fun » iso .inv » (a ∷_) $ xs
        ≡⟨⟩
          a ∷ (iso .fun » iso .inv $ xs)
        ≡⟨ cong (a ∷_) IHxs ⟩∎
          a ∷ xs
        ∎
        where
        p : trunc-cons a » iso .inv ≡ iso .inv » (a ∷_)
        p = trunc-comp-lemma (trunc-cons a » iso .inv) (iso .inv » (a ∷_)) FMSet.trunc p'
          where
          p' : ∣_∣₂ » trunc-cons a » iso .inv ≡ ∣_∣₂ » iso .inv » (a ∷_)
          p' =
              ∣_∣₂ » trunc-cons a » iso .inv
            ≡⟨⟩
              bag-cons a » ∣_∣₂ » iso .inv
            ≡⟨⟩
              bag-cons a » Colim.rec iso-inv-cocone
            ≡⟨ funExt $ Colim.elim depCocone ⟩∎
              Colim.rec iso-inv-cocone » (a ∷_) ∎
            ≡⟨⟩∎
              ∣_∣₂ » iso .inv » (a ∷_)
            where
            reflA : ∀ {ℓ} (A : Type ℓ) {x : A} → x ≡ x
            reflA _ = refl
            open DepCocone
            depCocone : DepCocone _ _ _ _
            depCocone .leg n l = refl
            depCocone .com idx = funExtDep (λ p → isProp→PathP (λ _ → FMSet.trunc _ _) refl refl)
           