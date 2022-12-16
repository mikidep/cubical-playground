open import CubicalPlayground.Prelude

open import Cubical.Foundations.Function using (idfun; _∘_; ∘-assoc)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.HITs.Colimit.Base
  using (Cocone; leg; com; colim; colim-leg; colim-com)
  renaming (rec to rec-colim)
open import Cubical.HITs.FiniteMultiset as FiniteMultiset using (FMSet; []; _∷_)
open import Cubical.HITs.SetTruncation
  using (∥_∥₂; ∣_∣₂; isSetSetTrunc)
  renaming (rec to rec-SetTrunc)

open import CubicalPlayground.LoopyChain.Base using (LoopyChain; AdjLoop)
open import CubicalPlayground.Endofunctor using (Endofunctor; iterate; iterate-endo)

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
      where
      swapᵢ : (n : ℕ) → bagChain-Ob (2 + n) → bagChain-Ob (2 + n)
      swapᵢ _ (cons a₁ (cons a₂ l)) = (cons a₂ (cons a₁ l))
      swapᵢ _ l = l
    bagChain-loop .(suc n) (F<$>idx n idx) = ListEndo <$> bagChain-loop n idx

  bag-colim = colim (asDiag bagChain)

  cons-n : ∀ n → A → bagChain .Ob n → bagChain .Ob (suc n)
  cons-n _ = cons

  bag-nil : bag-colim
  bag-nil = colim-leg 1 nil
  bag-cons : A → bag-colim → bag-colim
  bag-cons a = rec-colim cocone
    where
    open AdjLoop using (next; loopIdx)
    cocone : Cocone (ℓ-suc (ℓ-suc ℓ-zero)) (asDiag bagChain) bag-colim
    cocone .leg n = cons a » colim-leg (suc n)
    cocone .com {j = .n} (next n) =
        bagChain .ι n » cons-n (suc n) a » l (suc (suc n))
      ≡⟨ cong (λ f → f » l (suc (suc n))) top-comm ⟩
        cons-n n a » bagChain .ι (suc n) » l (suc (suc n))
      ≡⟨ »-assoc (cons-n n a) (bagChain .ι (suc n)) (l (suc (suc n))) ⟩
        cons-n n a » (bagChain .ι (suc n) » l (suc (suc n)))
      ≡⟨ cong (λ f → cons-n n a » f) bot-comm ⟩∎
        cons-n n a » l (suc n)
      ∎
      where
      l = colim-leg
      top-comm : bagChain .ι n » cons-n (suc n) a ≡ cons-n n a » bagChain .ι (suc n)
      top-comm = refl
      bot-comm : bagChain .ι (suc n) » l (suc (suc n)) ≡ l (suc n)
      bot-comm = colim-com (next (suc n))
    cocone .com {j = .n} (loopIdx n idx) =
        bagChain .loop n idx » cons-n n a » l (suc n)
      ≡⟨ cong (λ f → f » l (suc n)) (top-comm idx) ⟩
        cons-n n a » bagChain .loop (suc n) (F<$>idx n idx) » l (suc n)
      ≡⟨ »-assoc (cons-n n a) (bagChain .loop (suc n) (F<$>idx n idx)) (l (suc n)) ⟩
        cons-n n a » (bagChain .loop (suc n) (F<$>idx n idx) » l (suc n))
      ≡⟨ cong (λ f → cons-n n a » f) bot-comm ⟩∎
        cons-n n a » l (suc n)
      ∎
      where
      l = colim-leg
      top-comm : LoopIdx n
                → bagChain .loop n idx » cons-n n a
                  ≡ cons-n n a » bagChain .loop (suc n) (F<$>idx n idx)
      top-comm _ = refl
      bot-comm : bagChain .loop (suc n) (F<$>idx n idx) » l (suc n) ≡ l (suc n)
      bot-comm = colim-com (loopIdx (suc n) (F<$>idx n idx))



  -- bag-colim≃FMSet : bag-colim ≃ FMSet A
  -- bag-colim≃FMSet .fst = rec-colim cocone
  --   where
  --   cocone-leg : ∀ n → bagChain-Ob n → FMSet A
  --   cocone-leg (suc zero) nil = []
  --   cocone-leg (suc (suc n)) nil = []
  --   cocone-leg (suc (suc n)) (cons a l) = a ∷ cocone-leg (suc n) l
  --   open import Cubical.Data.Graph using (_<$>_)
  --   open AdjLoop using (next; loopIdx)
  --   cocone-com-next : ∀ n
  --     → cocone-leg (suc n) ∘ (asDiag bagChain <$> next n) ≡ cocone-leg n
  --   cocone-com-next zero = funExt λ ()
  --   cocone-com-next (suc zero) = funExt hom
  --     where
  --     hom : _
  --     hom nil = refl
  --   cocone-com-next (suc (suc n)) = funExt hom
  --     where
  --     hom : _
  --     hom nil = refl
  --     hom (cons a l) = cong (λ x → a ∷ x) (cocone-com-next (suc n) ≡$ l)
  --   cocone-com : ∀ {m n} (idx : AdjLoop LoopIdx m n)
  --     → cocone-leg n ∘ (asDiag bagChain <$> idx) ≡ cocone-leg m
  --   cocone-com {m = m} (next m) = cocone-com-next m
  --   -- cocone-com {m = .zero} (next zero) = funExt λ ()
  --   -- cocone-com {m = .1} (next (suc zero)) = funExt hom
  --   --   where
  --   --   hom : _
  --   --   hom nil = refl
  --   -- cocone-com {m = .(suc (suc m))} (next (suc (suc m))) = funExt hom
  --   --   where
  --   --   hom : _
  --   --   hom nil = refl
  --   --   hom (cons a l) = cong (λ x → a ∷ x) (cocone-com (next (suc m)) ≡$ l)
  --   cocone-com {m = m} (loopIdx m idx) = {!   !}
  --   cocone : Cocone ℓ-zero (asDiag bagChain) (FMSet A)
  --   cocone .leg = cocone-leg
  --   cocone .com = {!   !}
  -- bag-colim≃FMSet .snd = {!   !}

  -- isSetBag : isSet A → isSet bag-colim
  -- isSetBag isSetA x y p q = {!   !}


  rec-FMSet = FiniteMultiset.Rec.f
  
  -- FMSet≃bag-colim : isSet A → FMSet A ≃ bag-colim
  -- FMSet≃bag-colim isSetA .fst = rec-FMSet (isSetBag isSetA) {!   !} {!   !} {!   !}
  -- FMSet≃bag-colim isSetA .snd = {!   !}

  FMSet≃bag-colim : FMSet A ≃ ∥ bag-colim ∥₂
  FMSet≃bag-colim .fst = rec-FMSet
    isSetSetTrunc ∣ bag-nil ∣₂ embed-cons {!   !}
    where
    embed-cons : _
    embed-cons a = rec-SetTrunc isSetSetTrunc λ b → ∣ bag-cons a b ∣₂
  FMSet≃bag-colim .snd = {!   !}
