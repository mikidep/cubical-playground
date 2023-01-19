open import CubicalPlayground.Prelude

open import Cubical.Foundations.Function using (idfun; _∘_; ∘-assoc)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Functions.FunExtEquiv using (funExtDep)
open import Cubical.HITs.FiniteMultiset as FMSet using (FMSet; []; _∷_)
open import Cubical.HITs.SetTruncation as SetTrunc
  using (∥_∥₂; ∣_∣₂; isSetSetTrunc)

open import CubicalPlayground.LoopyChain.Base using (LoopyChain; AdjLoop)
open import CubicalPlayground.Endofunctor using (Endofunctor; iterate; iterate-endo)
open import CubicalPlayground.Colimit as Colim
  using (Cocone; leg; com; colim; colim-leg; colim-com; DepCocone)

module CubicalPlayground.Bag where

data LoopIdx : ℕ → Type where
  swapIdx : ∀ n → LoopIdx (2 + n)
  F<$>idx : ∀ n → LoopIdx n → LoopIdx (suc n)

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

  swapᵢ : (n : ℕ) → bagChain-Ob (2 + n) → bagChain-Ob (2 + n)
  swapᵢ _ (cons a₁ (cons a₂ l)) = (cons a₂ (cons a₁ l))
  swapᵢ _ l = l

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
    bagChain-loop .(2 + n) (swapIdx n) = swapᵢ n
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
--           → (cocone-leg (suc (suc n)) ∘ swapᵢ n) l ≡ cocone-leg (suc (suc n)) l
--         hom nil = refl
--         hom (cons a nil) = refl
--         hom (cons a (cons a₁ l)) = {!   !}
--       cocone-com-loop .(suc n) (F<$>idx n idx) = {!   !}

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
    dep-cocone .com {j = n} (next n) =
        bagChain .ι n » dep-cocone .leg (suc n)
      ≡[ p , B ]⟨ 
        funExtDep (λ {x₀ x₁} p → hom x₀ x₁ p)
      ⟩∎
        dep-cocone .leg n
      ∎
      where
      p = colim-com (next n)
      B = λ f → ∀ x → bag-cons a₁ (bag-cons a₂ (f x)) ≡ bag-cons a₂ (bag-cons a₁ (f x))
      hom : ∀ x₀ x₁ (p : x₀ ≡ x₁) → _
      hom x₀ x₁ p = sq
        where
        ι' = bagChain .ι
        l = colim-leg
        tl tr bl br : bag-colim
        tl = l (3 + n) (swapᵢ (suc n) $ ι' (2 + n) $ cons a₂ $ cons a₁ x₀)
        tr = l (3 + n) (ι' (2 + n) $ cons a₂ $ cons a₁ x₀)
        bl = l (2 + n) (swapᵢ n $ cons a₂ $ cons a₁ x₁)
        br = l (2 + n) (cons a₂ $ cons a₁ x₁)
        te : tl ≡ tr
        te = (λ i → colim-com (loopIdx (3 + n) (swapIdx (suc n))) i $ cons a₂ (cons a₁ (ι' n x₀)))
        be : bl ≡ br
        be = (λ i → colim-com (loopIdx (2 + n) (swapIdx n)) i $ cons a₂ (cons a₁ x₁))
        le : tl ≡ bl
        le = λ i → colim-com (next (2 + n)) i $ cons a₁ (cons a₂ (p i))
        re : tr ≡ br
        re = λ i → colim-com (next (2 + n)) i $ cons a₂ (cons a₁ (p i))
        sq' : le ∙ be ≡ te ∙ re
        sq' = {!   !}
        sq : Square te be le re
        sq = λ i → {!   !}
        -- sq i0 i0 = tl
        -- sq i0 i1 = bl
        -- sq i1 i0 = tr
        -- sq i1 i1 = br
    dep-cocone .com (loopIdx _ x) = {!   !}
  
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
