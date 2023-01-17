open import CubicalPlayground.Prelude

open import Cubical.Foundations.Function using (idfun; _∘_; ∘-assoc)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
open import Cubical.Data.Empty using (⊥) renaming (rec to rec-⊥)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Functions.FunExtEquiv using (funExtDep)
open import CubicalPlayground.Colimit
  using (Cocone; leg; com; colim; colim-leg; colim-com; DepCocone)
  renaming (rec to rec-colim; elim to elim-colim)
open import Cubical.HITs.FiniteMultiset as FMSet using (FMSet; []; _∷_)
open import Cubical.HITs.SetTruncation as SetTrunc
  using (∥_∥₂; ∣_∣₂; isSetSetTrunc)

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
  bag-cons-cocone : A → Cocone _ (asDiag bagChain) bag-colim
  bag-cons-cocone a .leg n = cons a » colim-leg (suc n)
  bag-cons-cocone a .com {j = .n} (next n) =
      bagChain .ι n » cons a » l (suc (suc n))
    ≡⟨ cong (_» l (suc (suc n))) top-comm ⟩
      cons a » bagChain .ι (suc n) » l (suc (suc n))
    ≡⟨ »-assoc (cons a) (bagChain .ι (suc n)) (l (suc (suc n))) ⟩
      cons a » (bagChain .ι (suc n) » l (suc (suc n)))
    ≡⟨ cong (cons a »_) bot-comm ⟩∎
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
    ≡⟨ cong (_» l (suc n)) (top-comm idx) ⟩
      cons a » bagChain .loop (suc n) (F<$>idx n idx) » l (suc n)
    ≡⟨ »-assoc (cons a) (bagChain .loop (suc n) (F<$>idx n idx)) (l (suc n)) ⟩
      cons a » (bagChain .loop (suc n) (F<$>idx n idx) » l (suc n))
    ≡⟨ cong (cons a »_) bot-comm ⟩∎
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

--   _++_ : bag-colim → bag-colim → bag-colim
--   b₁ ++ b₂ = rec-colim cocone b₁
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
--               bagChain .ι n » cocone-leg (suc n) » rec-colim (bag-cons-cocone a)
--             ≡⟨ cong (_» rec-colim (bag-cons-cocone a)) (cocone-com-next n) ⟩∎
--               cocone-leg n » rec-colim (bag-cons-cocone a) ∎
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

--   open AdjLoop
--   bag-eq : ∀ a₁ a₂ b → bag-cons a₁ (bag-cons a₂ b) ≡ bag-cons a₂ (bag-cons a₁ b)
--   bag-eq a₁ a₂ = auxb
--     where
--     auxb' : ∀ b → bag-cons a₁ (bag-cons a₂ b) ≡ bag-cons a₂ (bag-cons a₁ b)
--     auxb' b = {!   !}
--     
--     auxb : ∀ b → bag-cons a₁ (bag-cons a₂ b) ≡ bag-cons a₂ (bag-cons a₁ b)
--     auxb = elim-colim dep-cocone
--       where
--       open DepCocone
--       dep-cocone :
--         DepCocone
--           _
--           (asDiag bagChain)
--           _
--           (λ b → bag-cons a₁ (bag-cons a₂ b) ≡ bag-cons a₂ (bag-cons a₁ b))
--       dep-cocone .leg n l = colim-com (loopIdx (suc (suc n)) (swapIdx n)) ≡$ (cons a₂ (cons a₁ l))
      -- dep-cocone .com {j = n} (next n) =
      --     bagChain .ι n » dep-cocone .leg (suc n)
      --   ≡[ p , B ]⟨ 
      --   {!   !} -- cong {B = B} {!   !} p 
      --   ⟩∎
      --     dep-cocone .leg n
      --   ∎
      --   where
      --   p = colim-com (next n)
      --   B = λ f → ∀ x → bag-cons a₁ (bag-cons a₂ (f x)) ≡ bag-cons a₂ (bag-cons a₁ (f x))
      -- dep-cocone .com {j = .zero} (next zero) = funExtDep λ {x₀ = absurd} → rec-⊥ absurd 
      -- dep-cocone .com {j = .(suc n)} (next (suc n)) = {!   !} 
      -- dep-cocone .leg = dep-cocone-leg
      --   where
      --   dep-cocone-leg : ∀ n l →
      --     bag-cons a₁ (bag-cons a₂ (colim-leg n l)) ≡
      --     bag-cons a₂ (bag-cons a₁ (colim-leg n l))
      --   dep-cocone-leg zero = {!   !}
      --   dep-cocone-leg (suc n) = transport
      --     (cong (λ f → ∀ l → bag-cons a₁ (bag-cons a₂ (f l)) ≡ bag-cons a₂ (bag-cons a₁ (f l))) lemma-f)
      --     (f » dep-cocone-leg n)
      --     where
      --     f : bagChain .Ob (suc n) → bagChain-Ob n
      --     f = {!   !}
      --     lemma-f : f » colim-leg n ≡ colim-leg (suc n)
      --     lemma-f = {!   !}
      -- dep-cocone .com {j = n} (next n) = {!   !}
      -- dep-cocone .com (loopIdx _ x) = {!   !}
  
  SetTrunc-elim-Prop : ∀ {ℓ ℓ'} {A : Type ℓ} {P : ∥ A ∥₂ → Type ℓ'}
    → (∀ xt → isProp (P xt))
    → (∀ x → P ∣ x ∣₂)
    → ∀ xt → P xt
  SetTrunc-elim-Prop isPropP f = SetTrunc.elim (λ xt → isProp→isSet (isPropP xt)) f

  trunc-comp-lemma : ∀ {ℓ} {A B : Type ℓ} (f g : ∥ A ∥₂ → B)
    → isSet B
    → ∣_∣₂ » f ≡ ∣_∣₂ » g
    → f ≡ g
  trunc-comp-lemma {A = A} f g isSetB path = funExt hom
    where
    hom : (x : ∥ A ∥₂) → f x ≡ g x
    hom = SetTrunc-elim-Prop (λ _ → (isSetB _ _)) (path ≡$_)

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
    (funExt hom) ≡$_
    where
      hom : ∀ b → trunc-cons a₁ (trunc-cons a₂ ∣ b ∣₂) ≡ trunc-cons a₂ (trunc-cons a₁ ∣ b ∣₂)
      hom = elim-colim dep-cocone
        where
        open DepCocone
        dep-cocone : DepCocone _  (asDiag bagChain) _ _
        dep-cocone .leg n l =
          cong ∣_∣₂ (colim-com (loopIdx (suc (suc n)) (swapIdx n)) ≡$ (cons a₂ (cons a₁ l)))
        dep-cocone .com f = funExtDep (λ p → isProp→PathP (λ i → isSetSetTrunc _ _) _ _)

  FMSet≃bag-colim : FMSet A ≃ trunc-colim
  FMSet≃bag-colim = isoToEquiv iso
    where
    open Iso
    iso : Iso (FMSet A) trunc-colim
    iso .fun = FMSet.Rec.f
      isSetSetTrunc ∣ bag-nil ∣₂ trunc-cons trunc-eq
    iso .inv = SetTrunc.rec FMSet.trunc (rec-colim cocone)
      where
      cocone-leg : ∀ n → iterate (ListEndo .F) n ⊥ → FMSet A
      cocone-leg zero = λ ()
      cocone-leg (suc n) nil = []
      cocone-leg (suc n) (cons a x) = a ∷ cocone-leg n x
      cocone-com-ι : ∀ n → bagChain .ι n » cocone-leg (suc n) ≡ cocone-leg n
      cocone-com-ι zero = funExt λ ()
      cocone-com-ι (suc n) = funExt hom
        where
        hom : ∀ l → _
        hom nil = refl
        hom (cons a x) = cong (a ∷_) (cocone-com-ι n ≡$ x)
      cocone-com-loop : ∀ n idx → bagChain .loop n idx » cocone-leg n ≡ cocone-leg n
      cocone-com-loop .(2 + n) (swapIdx n) = funExt hom
        where
        hom : _
        hom nil = refl
        hom (cons a nil) = refl
        hom (cons a₁ (cons a₂ l)) = FMSet.comm a₂ a₁ (cocone-leg n l)
      cocone-com-loop .(suc n) (F<$>idx n idx) = funExt hom
        where
        hom : _
        hom nil = refl
        hom (cons a x) = cong (a ∷_) (cocone-com-loop n idx ≡$ x)
      cocone : Cocone _ (asDiag bagChain) (FMSet A)
      cocone .leg = cocone-leg
      cocone .com {j = n} (next .n) = cocone-com-ι n
      cocone .com {j = n} (loopIdx .n idx) = cocone-com-loop n idx
    iso .rightInv = {!   !} -- trunc-comp-lemma
--       {!   !}
--       {!   !}
--       {!   !}
--       {!   !}
--       {!   !}
--       {!   !}
    -- SetTrunc.elim (λ b → isProp→isSet {! isSetSetTrunc  !}) {!   !}
    iso .leftInv = {!   !}
 