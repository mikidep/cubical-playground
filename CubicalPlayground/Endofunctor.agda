open import CubicalPlayground.Prelude
open import Cubical.Foundations.Function using (idfun; _∘_)
open import Cubical.Foundations.GroupoidLaws using (rUnit; lUnit; assoc; congFunct)
open import Cubical.Functions.FunExtEquiv using (funExt₂)
open import Cubical.Data.Nat using (ℕ; zero; suc)

module CubicalPlayground.Endofunctor {ℓ : _} where

record Endofunctor : Type (ℓ-suc ℓ) where
  constructor cons-Endo
  field
    F : Type ℓ → Type ℓ
    _<$>_ : {A B : Type ℓ} → (A → B) → F A → F B
    hom-id : {A : Type ℓ} → (_<$>_ (idfun A)) ≡ idfun _
    hom-∘ : {A B C : Type ℓ} (f : A → B) (g : B → C)
      → (_<$>_ g) ∘ (_<$>_ f) ≡ _<$>_ (g ∘ f)
  infixr 10 _<$>_
open Endofunctor

idF : Endofunctor
idF .F = idfun _
idF ._<$>_ = idfun _
idF .hom-id = refl
idF .hom-∘ f g = refl

infixr 11 _∘F_
_∘F_ : Endofunctor → Endofunctor → Endofunctor
(F ∘F G) .F = (F .Endofunctor.F) ∘ (G .Endofunctor.F)
(F ∘F G) <$> f = F <$> (G <$> f)

--    F <$> (G <$> idfun _)
--  ≡⟨ cong (F ._<$>_) (G .hom-id) ⟩
--    F <$> (idfun _)
--  ≡⟨ F .hom-id ⟩∎
--    idfun _ ∎
(F ∘F G) .hom-id = cong (F ._<$>_) (G .hom-id) ∙ F .hom-id
(F ∘F G) .hom-∘ f g = outer-hom ∙ cong (F ._<$>_) inner-hom
  where
  outer-hom : (F <$> G <$> g) ∘ (F <$> G <$> f) ≡ (F <$> ((G <$> g) ∘ (G <$> f)))
  outer-hom = F .hom-∘ (G <$> f) (G <$> g)
  inner-hom : (G <$> g) ∘ (G <$> f) ≡ G <$> (g ∘ f)
  inner-hom = G .hom-∘ f g

EndoPathP :
  {E E' : Endofunctor}
  (Fp : E .F ≡ E' .F)
  (mapp : PathP (λ i → {A B : Type ℓ} → (A → B) → (Fp i) A → (Fp i) B) (E ._<$>_) (E' ._<$>_))
  (hom-id-p : PathP (λ i → {A : Type ℓ} → (mapp i (idfun A)) ≡ idfun _) (E .hom-id) (E' .hom-id))
  (hom-∘-p : PathP (λ i → {A B C : Type ℓ} (f : A → B) (g : B → C)
      → (mapp i g) ∘ (mapp i f) ≡ mapp i (g ∘ f)) (E .hom-∘) (E' .hom-∘))
  → E ≡ E'
EndoPathP Fp mapp hom-id-p hom-∘-p = λ i → cons-Endo (Fp i) (mapp i) (hom-id-p i) (hom-∘-p  i)

{- EndoPathPExt :
  {E E' : Endofunctor}
  (Fp : E .F ≡ E' .F)
  (mappExt : {A B : Type ℓ} → PathP (λ i → (A → B) → (Fp i) A → (Fp i) B) (E ._<$>_ {A} {B}) (E' ._<$>_ {A} {B}))
  → {!   !}
  → {!   !}
  → E ≡ E'
EndoPathPExt Fp mappExt hom-id-pExt hom-∘-pExt =
  EndoPathP
    Fp
    {!   !}
    (λ i {A} {B} → mappExt {A} {B} i) {!   !} {!   !} -}

endo-∘-id-l : (E : Endofunctor) → idF ∘F E ≡ E
endo-∘-id-l E = EndoPathP
  refl 
  refl 
  (implicitFunExt λ {A} →
      E .hom-id {A = A} ∙ refl
    ≡⟨ sym (rUnit _) ⟩∎
      (E .hom-id {A = A})
    ∎
  )
  (implicitFunExt (λ {A} → implicitFunExt λ {B} → implicitFunExt λ {C} → 
      funExt₂ (λ f g → refl ∙ E .hom-∘ f g ≡⟨ sym (lUnit _) ⟩∎ E .hom-∘ f g ∎)))

endo-∘-id-r : (E : Endofunctor) → E ∘F idF ≡ E
endo-∘-id-r E = EndoPathP
  refl 
  refl 
  (implicitFunExt λ {A} →
      refl ∙ E .hom-id {A = A}
    ≡⟨ sym (lUnit _) ⟩∎
      (E .hom-id {A = A})
    ∎
  )
  (implicitFunExt λ {A} → implicitFunExt λ {B} → implicitFunExt λ {C} → 
      funExt₂ λ f g → E .hom-∘ f g ∙ refl ≡⟨ sym (rUnit _) ⟩∎ E .hom-∘ f g ∎)

endo-∘-assoc : (E G H : Endofunctor) → (E ∘F G) ∘F H ≡ E ∘F (G ∘F H)
endo-∘-assoc E G H = EndoPathP
  refl
  refl
  (implicitFunExt λ {A} →
      cong ((E ∘F G) ._<$>_) (H .hom-id) ∙ cong (E ._<$>_) (G .hom-id) ∙ (E .hom-id)
    ≡⟨⟩
      cong (E ._<$>_ ∘ G ._<$>_) (H .hom-id) ∙ cong (E ._<$>_) (G .hom-id) ∙ (E .hom-id)
    ≡⟨ cong (λ p → p ∙ cong (E ._<$>_) (G .hom-id) ∙ (E .hom-id)) (cong-∘ (E ._<$>_)(G ._<$>_) (H .hom-id)) ⟩
      cong (E ._<$>_) (cong (G ._<$>_) (H .hom-id)) ∙ cong (E ._<$>_) (G .hom-id) ∙ (E .hom-id)
    ≡⟨ assoc _ _ _ ⟩
      (cong (E ._<$>_) (cong (G ._<$>_) (H .hom-id)) ∙ cong (E ._<$>_) (G .hom-id)) ∙ (E .hom-id)
    ≡⟨ cong (λ p → p ∙ (E .hom-id)) (sym (congFunct (E ._<$>_) (cong (G ._<$>_) (H .hom-id)) (G .hom-id))) ⟩∎
      cong (E ._<$>_) (cong (G ._<$>_) (H .hom-id) ∙ G .hom-id) ∙ (E .hom-id)
    ∎)
  (implicitFunExt λ {A} → implicitFunExt λ {B} → implicitFunExt λ {C} → 
    funExt₂ λ f g → 
        (E ∘F G) .hom-∘ (H <$> f) (H <$> g) ∙ cong ((E ∘F G) ._<$>_) (H .hom-∘ f g)
      ≡⟨⟩
        (E ∘F G) .hom-∘ (H <$> f) (H <$> g) ∙ cong (E ._<$>_ ∘ G ._<$>_) (H .hom-∘ f g)
      ≡⟨⟩
        (E .hom-∘ (G ∘F H <$> f) (G ∘F H <$> g) ∙ cong (E ._<$>_) (G .hom-∘ (H <$> f) (H <$> g))) ∙ cong (E ._<$>_ ∘ G ._<$>_) (H .hom-∘ f g)
      ≡⟨ sym (assoc _ _ _) ⟩
        E .hom-∘ (G ∘F H <$> f) (G ∘F H <$> g) ∙ cong (E ._<$>_) (G .hom-∘ (H <$> f) (H <$> g)) ∙ cong (E ._<$>_ ∘ G ._<$>_) (H .hom-∘ f g)
      ≡⟨ cong (λ p → E .hom-∘ (G ∘F H <$> f) (G ∘F H <$> g) ∙ cong (E ._<$>_) (G .hom-∘ (H <$> f) (H <$> g)) ∙ p) (cong-∘ (E ._<$>_) (G ._<$>_) _) ⟩
        E .hom-∘ (G ∘F H <$> f) (G ∘F H <$> g) ∙ cong (E ._<$>_) (G .hom-∘ (H <$> f) (H <$> g)) ∙ cong (E ._<$>_) (cong (G ._<$>_) (H .hom-∘ f g))
      ≡⟨ cong (λ p → (E .hom-∘ (G ∘F H <$> f) (G ∘F H <$> g)) ∙ p) (sym (congFunct (E ._<$>_) _ _)) ⟩∎
        E .hom-∘ (G ∘F H <$> f) (G ∘F H <$> g) ∙ cong (E ._<$>_) (G .hom-∘ (H <$> f) (H <$> g) ∙ cong (G ._<$>_) (H .hom-∘ f g))
  {-  ≡⟨⟩
        (E .hom-∘ (G ∘F H <$> f) (G ∘F H <$> g)) ∙ cong (E ._<$>_) ((G ∘F H) .hom-∘ f g) -}
      ∎)
  where
  cong-∘ : {ℓ₁ ℓ₂ ℓ₃ : _} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (f : B → C) (g : A → B) {x y : A} (p : x ≡ y)
    → cong (f ∘ g) p ≡ cong f (cong g p)
  cong-∘ f g p = refl

iterate : {X : Type ℓ} → (X → X) → ℕ → X → X
iterate f zero = idfun _
iterate f (suc n) = f ∘ (iterate f n)

iterate-endo-outer : Endofunctor → ℕ → Endofunctor
iterate-endo-outer F zero = idF
iterate-endo-outer F (suc n) = F ∘F (iterate-endo-outer F n)

iterate-endo-inner : Endofunctor → ℕ → Endofunctor
iterate-endo-inner F zero = idF
iterate-endo-inner F (suc n) = (iterate-endo-inner F n) ∘F F

iterate-endo = iterate-endo-outer

it-endo-outer≡inner : (F : Endofunctor) (n : ℕ) → iterate-endo-outer F n ≡ iterate-endo-inner F n
it-endo-outer≡inner F zero = refl
it-endo-outer≡inner F (suc zero) =
    F ∘F idF
  ≡⟨ endo-∘-id-r F ⟩
    F
  ≡⟨ sym (endo-∘-id-l F) ⟩∎
    idF ∘F F
  ∎
it-endo-outer≡inner F (suc (suc n)) = 
    (F ∘F (iterate-endo-outer F (suc n)))
  ≡⟨ cong (_∘F_ F) (it-endo-outer≡inner F (suc n)) ⟩
    (F ∘F (iterate-endo-inner F (suc n)))
  ≡⟨⟩
    F ∘F iterate-endo-inner F n ∘F F
  ≡⟨ cong (λ E → F ∘F E ∘F F) (sym (it-endo-outer≡inner F n)) ⟩
    F ∘F iterate-endo-outer F n ∘F F
  ≡⟨ sym (endo-∘-assoc F (iterate-endo-outer F n) F) ⟩
    (F ∘F iterate-endo-outer F n) ∘F F
  ≡⟨⟩
    ((iterate-endo-outer F (suc n)) ∘F F)
  ≡⟨ cong (λ x → _∘F_ x F) (it-endo-outer≡inner F (suc n)) ⟩∎
    (iterate-endo-inner F (suc n)) ∘F F
  ∎

