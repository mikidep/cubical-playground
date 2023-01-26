open import CubicalPlayground.Prelude hiding (_$_)
open import Cubical.Data.Graph

module CubicalPlayground.Colimit where

open import Cubical.HITs.Colimit.Base public

record DepCocone ℓ
  {ℓd ℓv ℓe ℓx}
  {I : Graph ℓv ℓe}
  (F : Diag ℓd I)
  {X : Type ℓx}
  (C : Cocone ℓx F X)
  (P : X → Type ℓ)
  : Type (ℓ-suc (ℓ-max ℓ (ℓ-max (ℓ-max ℓv ℓe) (ℓ-suc ℓd)))) where
  field
    leg : ∀ (j : Node I) → (x : F $ j) → P (C .leg j x)
    com : ∀ {j k} (f : Edge I j k) → F <$> f » leg k ≡[ (C .com f), (λ f → ∀ x → P (f x)) ] leg j

open DepCocone

elim :
  ∀ {ℓ ℓd ℓv ℓe}
  {I : Graph ℓv ℓe}
  {F : Diag ℓd I}
  {P : colim F → Type ℓ}
  → DepCocone _ F (colimCone) P
  → (x : colim F) → P x
elim DC (colim-leg j A) = DC .leg j A
elim DC (colim-com f i A) = DC .com f i A

module _ where
  open Graph

  com-∘ : 
    ∀ {ℓd ℓv ℓe}
    {I : Graph ℓv ℓe}
    {F : Diag ℓd I}
    {i j k : I .Node}
    (e : I .Edge i j)
    (f : I .Edge j k)
    → F <$> e » F <$> f » colim-leg {F = F} k ≡ colim-leg i
  com-∘ {F = F} {i = i} {j = j} {k = k} e f = cong ((F <$> e) »_) (colim-com f) ∙ colim-com e 
