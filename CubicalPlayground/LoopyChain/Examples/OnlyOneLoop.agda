open import CubicalPlayground.Prelude

open import Cubical.Foundations.Function using (idfun; _∘_)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Bool using (Bool; true; false; false≢true)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.HITs.Colimit.Base
  using (Cocone; leg; com; colim; colim-leg; colim-com)
  renaming (rec to rec-colim)

open import CubicalPlayground.LoopyChain.Base using (LoopyChain; next; loopIdx)
open import CubicalPlayground.Endofunctor using (Endofunctor; iterate; iterate-endo)

module CubicalPlayground.LoopyChain.Examples.OnlyOneLoop where

data LoopIdx : ℕ → Type where
  onlyIdx : LoopIdx 3

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

  bagChain : LoopyChain LoopIdx
  bagChain .Ob n = iterate (ListEndo .F) n ⊥
  bagChain .ι = ι-aux
    where
    ! : ⊥ → ListEndo .F ⊥
    ! ()
    ι-aux : (n : ℕ) → iterate (ListEndo .F) n ⊥ → ListEndo .F (iterate (ListEndo .F) n ⊥)
    ι-aux zero = !
    ι-aux (suc n) = ListEndo <$> ι-aux n
  -- bagChain .Ob n = (ListEndo^ n .F) ⊥
  -- bagChain .ι n = ListEndo^ n <$> !
  -- bagChain .ι n = transport (cong (λ it → it n .F ⊥ → it (suc n) .F ⊥) inner≡outer) ι-inner -- ListEndo^ n <$> !
  --   ListEndo^inner = iterate-endo-inner ListEndo
  --   ι-inner : ListEndo^inner n .F ⊥ → ListEndo^inner (suc n) .F ⊥
  --   ι-inner = ListEndo^inner n <$> !
  --   inner≡outer : ListEndo^inner ≡ ListEndo^
  --   inner≡outer = funExt (λ n → sym (it-endo-outer≡inner ListEndo n))
  bagChain .loop .3 onlyIdx = swapᵢ {0}
    where
    swapᵢ : {n : ℕ} → bagChain .Ob (suc (suc (suc n))) → bagChain .Ob (suc (suc (suc n)))
    swapᵢ (cons a₁ (cons a₂ l)) = (cons a₂ (cons a₁ l))
    swapᵢ l = l

  colimBagChain : Type₂
  colimBagChain = colim (asDiag bagChain)

module Inequality where
  colim-Bool : Type₂
  colim-Bool = colimBagChain Bool

  l-tf : colim-Bool
  l-tf = colim-leg 3 (cons true (cons false nil))

  l-ft : colim-Bool
  l-ft = colim-leg 3 (cons false (cons true nil))

  tf≡ft : l-tf ≡ l-ft
  tf≡ft = colim-com (loopIdx 3 onlyIdx) ≡$ (cons false (cons true nil))

  l-ttf : colim-Bool
  l-ttf = colim-leg 4 (cons true (cons true (cons false nil)))

  l-tft : colim-Bool
  l-tft = colim-leg 4 (cons true (cons false (cons true nil)))

  ttf≢tft : ¬ l-ttf ≡ l-tft
  ttf≢tft path = false≢true false≡true
    where
    false≡true : false ≡ true
    false≡true = cong drop2-take1 path
      where
      drop2-take1 : colim-Bool → Bool
      drop2-take1 = rec-colim cocone
        where
        open Endofunctor
        cocone : Cocone ℓ-zero (LoopyChain.asDiag (bagChain Bool)) Bool
        cocone .leg (suc (suc (suc (suc _)))) list with list
        ... | cons _ (cons _ (cons b _)) = b
        ... | _ = true
        cocone .leg _ _ = true
        cocone .com {j = .3} {k = .3} (loopIdx .3 onlyIdx) = refl
        cocone .com {j = .zero} {k = .1} (next zero) = refl
        cocone .com {j = .1} {k = .2} (next (suc zero)) = refl
        cocone .com {j = .2} {k = .3} (next (suc (suc zero))) = refl
        cocone .com {j = .(suc (suc (suc m)))} {k = .(suc (suc (suc (suc m))))} (next (suc (suc (suc m)))) = funExt (aux m)
          where
          aux : (m' : ℕ) (l : iterate (ListEndo Bool .F) (suc (suc (suc m'))) $ ⊥)
            → cocone .leg (suc (suc (suc (suc m')))) (bagChain Bool .ι (suc (suc (suc m'))) l)
                ≡ cocone .leg (suc (suc (suc m'))) l
          aux zero nil = refl
          aux zero (cons a nil) = refl
          aux zero (cons a (cons a₁ nil)) = refl
          aux (suc m') nil = refl
          aux (suc m') (cons a nil) = refl
          aux (suc m') (cons a (cons a₁ nil)) = refl
          aux (suc m') (cons a (cons a₁ (cons a₂ x))) = refl
      