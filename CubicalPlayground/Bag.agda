open import CubicalPlayground.Prelude

open import Cubical.Foundations.Function using (idfun; _∘_; ∘-assoc)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import CubicalPlayground.Colimit
  using (Cocone; leg; com; colim; colim-leg; colim-com; DepCocone)
  renaming (rec to rec-colim; elim to elim-colim)
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

  ι-cons-comm : ∀ n a → bagChain .ι n » cons a ≡ cons a » bagChain .ι (suc n)
  ι-cons-comm n a = refl

  bag-nil : bag-colim
  bag-nil = colim-leg 1 nil

  open AdjLoop using (next; loopIdx)
  bag-cons-cocone : A → Cocone (ℓ-suc (ℓ-suc ℓ-zero)) (asDiag bagChain) bag-colim
  bag-cons-cocone a .leg n = cons a » colim-leg (suc n)
  bag-cons-cocone a .com {j = .n} (next n) =
      bagChain .ι n » cons a » l (suc (suc n))
    ≡⟨ cong (λ f → f » l (suc (suc n))) top-comm ⟩
      cons a » bagChain .ι (suc n) » l (suc (suc n))
    ≡⟨ »-assoc (cons a) (bagChain .ι (suc n)) (l (suc (suc n))) ⟩
      cons a » (bagChain .ι (suc n) » l (suc (suc n)))
    ≡⟨ cong (λ f → cons a » f) bot-comm ⟩∎
      cons a » l (suc n)
    ∎
    where
    l = colim-leg
    top-comm : bagChain .ι n » cons a ≡ cons a » bagChain .ι (suc n)
    top-comm = ι-cons-comm n a
    bot-comm : bagChain .ι (suc n) » l (suc (suc n)) ≡ l (suc n)
    bot-comm = colim-com (next (suc n))
  bag-cons-cocone a .com {j = .n} (loopIdx n idx) =
      bagChain .loop n idx » cons a » l (suc n)
    ≡⟨ cong (λ f → f » l (suc n)) (top-comm idx) ⟩
      cons a » bagChain .loop (suc n) (F<$>idx n idx) » l (suc n)
    ≡⟨ »-assoc (cons a) (bagChain .loop (suc n) (F<$>idx n idx)) (l (suc n)) ⟩
      cons a » (bagChain .loop (suc n) (F<$>idx n idx) » l (suc n))
    ≡⟨ cong (λ f → cons a » f) bot-comm ⟩∎
      cons a » l (suc n)
    ∎
    where
    l = colim-leg
    top-comm : LoopIdx n
              → bagChain .loop n idx » cons a
                ≡ cons a » bagChain .loop (suc n) (F<$>idx n idx)
    top-comm _ = refl
    bot-comm : bagChain .loop (suc n) (F<$>idx n idx) » l (suc n) ≡ l (suc n)
    bot-comm = colim-com (loopIdx (suc n) (F<$>idx n idx))
  bag-cons : A → bag-colim → bag-colim
  bag-cons a = rec-colim (bag-cons-cocone a)
    -- where

  _++_ : bag-colim → bag-colim → bag-colim
  b₁ ++ b₂ = rec-colim cocone b₁
    where
    cocone-leg : (n : ℕ) → bagChain-Ob n → bag-colim
    cocone-leg (suc n) nil = b₂
    cocone-leg (suc n) (cons a l) = bag-cons a (cocone-leg n l)
    open AdjLoop
    cocone : Cocone (ℓ-suc (ℓ-suc ℓ-zero)) (asDiag bagChain) bag-colim
    cocone .leg = cocone-leg
    cocone .com {j = n} (next .n) = cocone-com-next n
      where
      cocone-com-next : ∀ n
        →  bagChain .ι n » cocone .leg (suc n) ≡ cocone .leg n
      cocone-com-next zero = funExt λ ()
      cocone-com-next (suc n) = funExt hom
        where
        hom : ∀ l
          → bagChain .ι (suc n) » cocone-leg (suc (suc n)) $ l ≡ cocone-leg (suc n) l
        hom nil = refl
        hom (cons a l) = path ≡$ l
          where
          path : cons a » bagChain .ι (suc n) » cocone-leg (suc (suc n)) ≡ cons a » cocone-leg (suc n)
          path =
              cons a » bagChain .ι (suc n) » cocone-leg (suc (suc n))
            ≡⟨ cong (λ f → f » cocone-leg (suc (suc n))) (sym $ ι-cons-comm n a) ⟩
              bagChain .ι n » cons a » cocone-leg (suc (suc n))
            ≡⟨⟩
              bagChain .ι n » cocone-leg (suc n) » rec-colim (bag-cons-cocone a)
            ≡⟨ cong (λ f → f » rec-colim (bag-cons-cocone a)) (cocone-com-next n) ⟩∎
              cocone-leg n » rec-colim (bag-cons-cocone a) ∎
            ≡⟨⟩∎
              cons a » cocone-leg (suc n)
    cocone .com {j = n} (loopIdx .n idx) = cocone-com-loop n idx
      where
      cocone-com-loop : ∀ n (idx : LoopIdx n)
        → cocone-leg n ∘ bagChain .loop n idx ≡ cocone-leg n
      cocone-com-loop .(2 + n) (swapIdx n) = funExt hom
        where
        hom : ∀ l
          → (cocone-leg (suc (suc n)) ∘ swapᵢ n) l ≡ cocone-leg (suc (suc n)) l
        hom nil = refl
        hom (cons a nil) = refl
        hom (cons a (cons a₁ l)) = {!   !}
      cocone-com-loop .(suc n) (F<$>idx n idx) = {!   !}

  open AdjLoop
  bag-eq : ∀ a₁ a₂ b → bag-cons a₁ (bag-cons a₂ b) ≡ bag-cons a₂ (bag-cons a₁ b)
  bag-eq a₁ a₂ = auxb
    where
    auxb : ∀ b → bag-cons a₁ (bag-cons a₂ b) ≡ bag-cons a₂ (bag-cons a₁ b)
    auxb = elim-colim dep-cocone
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
        ≡[ colim-com (next n) , (λ f → ∀ x → bag-cons a₁ (bag-cons a₂ (f x)) ≡ bag-cons a₂ (bag-cons a₁ (f x))) ]⟨ {!   !} ⟩∎
          dep-cocone .leg n
        ∎
      dep-cocone .com (loopIdx _ x) = {!   !}

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
    