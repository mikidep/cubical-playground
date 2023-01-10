open import CubicalPlayground.Prelude

open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.HITs.Colimit.Base
  using (Cocone; leg; com; colim; colim-leg; colim-com)
  renaming (rec to rec-colim)

open import CubicalPlayground.LoopyChain.Base using (LoopyChain; AdjLoop)
open import CubicalPlayground.Endofunctor using (Endofunctor; iterate; iterate-endo)

module CubicalPlayground.OneEq (depth : ℕ) where

data LoopIdx : ℕ → Type where
  eqIdx : ∀ n → LoopIdx (depth + n)
  F<$>idx : ∀ n → LoopIdx n → LoopIdx (suc n)

open LoopyChain

module _ (A : Type) (B : A → Type) where
  data PolyF {ℓ} (X : Type ℓ) : Type ℓ where
    cons : (op : A) (args : B op → X) → PolyF X
  
  PolyF-map : {X Y : Type} → (X → Y) → PolyF X → PolyF Y
  PolyF-map f (cons op args) = cons op (args » f)

  open Endofunctor

  PolyEndo : Endofunctor
  PolyEndo .F = PolyF
  PolyEndo <$> f = PolyF-map f
  PolyEndo .hom-id = funExt hom
    where
    hom : _
    hom (cons _ _) = refl
  hom-∘ PolyEndo f g = funExt hom
    where
    hom : _
    hom (cons _ _) = refl

  PolyEndo^ : ℕ → Endofunctor
  PolyEndo^ = iterate-endo PolyEndo


  oneEqChain-Ob : ℕ → Type
  oneEqChain-Ob n = iterate (PolyEndo .F) n ⊥

  module _
    (eq-fₙ : ∀ n
          → oneEqChain-Ob (depth + n)
          → oneEqChain-Ob (depth + n)) where

    oneEqChain : LoopyChain LoopIdx
    oneEqChain .Ob = oneEqChain-Ob
    oneEqChain .ι = oneEqChain-ι
      where
      ! : ⊥ → PolyEndo .F ⊥
      ! ()
      oneEqChain-ι : (n : ℕ) → iterate (PolyEndo .F) n ⊥ → PolyEndo .F (iterate (PolyEndo .F) n ⊥)
      oneEqChain-ι zero = !
      oneEqChain-ι (suc n) = PolyEndo <$> oneEqChain-ι n
    oneEqChain .loop = oneEqChain-loop
      where
      oneEqChain-loop : ∀ n → LoopIdx n → oneEqChain-Ob n → oneEqChain-Ob n
      oneEqChain-loop .(depth + n) (eqIdx n) = eq-fₙ n
      oneEqChain-loop .(suc n) (F<$>idx n idx) = PolyEndo <$> oneEqChain-loop n idx

    chain-colim = colim (asDiag oneEqChain)

    colim-cons : PolyF chain-colim → chain-colim
    colim-cons (cons op args) = colim-leg {!   !} {!   !}
