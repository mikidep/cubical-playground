{-# OPTIONS --postfix-projections #-}

open import CubicalPlayground.Prelude
open import Cubical.Foundations.Prelude using (_∎)
open import Cubical.HITs.Colimit.Base
open import Cubical.Data.Graph.Base renaming (_<$>_ to _<$>'_)
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Fin
open import Cubical.Core.Primitives
open import Cubical.Foundations.Function
open import Cubical.Functions.FunExtEquiv using (funExtDep; funExt₂)
open import Cubical.Relation.Nullary using (Dec; yes; no; mapDec; ¬_)
open import Cubical.Foundations.GroupoidLaws

module CubicalPlayground.colim-weird-chain where

data Adj : ℕ → ℕ → Type where
  same : (n : ℕ) → Adj n n 
  next : (n : ℕ) → Adj n (suc n)

areAdj : ∀ m n → Dec (Adj m n)
areAdj zero zero          = yes (same zero)
areAdj zero (suc zero)    = yes (next zero)
areAdj zero (suc (suc n)) = no λ ()
areAdj (suc m) zero       = no λ ()
areAdj (suc m) (suc n)    = mapDec {A = Adj m n} preserves preserves-¬ dec
  where
  preserves : (x : Adj m n) → Adj (suc m) (suc n)
  preserves (same .m) = same (suc m)
  preserves (next .m) = next (suc m)
  preserves-¬ : ¬ (Adj m n) → ¬ (Adj (suc m) (suc n))
  preserves-¬ ¬-adj (same .(suc m)) = ¬-adj (same m)
  preserves-¬ ¬-adj (next .(suc m)) = ¬-adj (next m)
  dec : Dec (Adj m n)
  dec = areAdj m n

LoopyChainGraph : (LoopIdx : (n : ℕ) → Type) → Graph _ _
LoopyChainGraph LoopIdx .Node = ℕ
LoopyChainGraph LoopIdx .Edge m n with areAdj m n
... | yes (same .m) = LoopIdx m
... | yes (next .m) = Unit
... | no _ = ⊥

LoopyChainGraph' : (LoopIdx : (n : ℕ) → Type) → Graph _ _
LoopyChainGraph' LoopIdx .Node = ℕ
LoopyChainGraph' LoopIdx .Edge m n = {! areAdj m n  !}
  where
  aux : {!   !} → Type
  aux = {!   !}

record LoopyChain (LoopIdx : (n : ℕ) → Type) : Type₁ where
  field
    Ob : ℕ → Type
    ι : (n : ℕ) → Ob n → Ob (suc n)
    loop : (n : ℕ) → LoopIdx n → Ob n → Ob n
  
  asDiag : Diag _ (LoopyChainGraph LoopIdx)
  asDiag $ n = Ob n
  asDiag ._<$>'_ {m} {n} x with areAdj m n
  ... | yes (same .m) = loop m x
  ... | yes (next .m) = ι m
open LoopyChain

module _ {ℓ : _} where
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

  iterate : {ℓ : _} {X : Type ℓ} → (X → X) → ℕ → X → X
  iterate f zero = idfun _
  iterate f (suc n) = f ∘ (iterate f n)

  iterate-endo : Endofunctor → ℕ → Endofunctor
  iterate-endo F zero = idF
  iterate-endo F (suc n) = F ∘F (iterate-endo F n)

  iterate-endo-inner : Endofunctor → ℕ → Endofunctor
  iterate-endo-inner F zero = idF
  iterate-endo-inner F (suc n) = (iterate-endo-inner F n) ∘F F

  it-endo-outer≡inner : (F : Endofunctor) (n : ℕ) → iterate-endo F n ≡ iterate-endo-inner F n
  it-endo-outer≡inner F zero = refl
  it-endo-outer≡inner F (suc zero) =
      F ∘F idF
    ≡⟨ endo-∘-id-r F ⟩
      F
    ≡⟨ sym (endo-∘-id-l F) ⟩∎
      idF ∘F F
    ∎
  it-endo-outer≡inner F (suc (suc n)) = 
      (F ∘F (iterate-endo F (suc n)))
    ≡⟨ cong (_∘F_ F) (it-endo-outer≡inner F (suc n)) ⟩
      (F ∘F (iterate-endo-inner F (suc n)))
    ≡⟨⟩
      F ∘F iterate-endo-inner F n ∘F F
    ≡⟨ cong (λ E → F ∘F E ∘F F) (sym (it-endo-outer≡inner F n)) ⟩
      F ∘F iterate-endo F n ∘F F
    ≡⟨ sym (endo-∘-assoc F (iterate-endo F n) F) ⟩
      (F ∘F iterate-endo F n) ∘F F
    ≡⟨⟩
      ((iterate-endo F (suc n)) ∘F F)
    ≡⟨ cong (λ x → _∘F_ x F) (it-endo-outer≡inner F (suc n)) ⟩∎
      (iterate-endo-inner F (suc n)) ∘F F
    ∎

data BagLoopIdx : ℕ → Type where
  onlyIdx : BagLoopIdx 3

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

  bagChain : LoopyChain BagLoopIdx
  bagChain .Ob n = (ListEndo^ n .F) ⊥
  bagChain .ι n = transport (cong (λ it → it n .F ⊥ → it (suc n) .F ⊥) inner≡outer) ι-inner -- ListEndo^ n <$> !
    where
    ListEndo^inner = iterate-endo-inner ListEndo
    ! : ⊥ → ListEndo .F ⊥
    ! ()
    ι-inner : ListEndo^inner n .F ⊥ → ListEndo^inner (suc n) .F ⊥
    ι-inner = ListEndo^inner n <$> !
    inner≡outer : ListEndo^inner ≡ ListEndo^
    inner≡outer = funExt (λ n → sym (it-endo-outer≡inner ListEndo n))
  bagChain .loop .3 onlyIdx = swap₃ 
    where
    swap₃ : bagChain .Ob 3 → bagChain .Ob 3
    swap₃ (cons a₁ (cons a₂ nil)) = (cons a₂ (cons a₁ nil))
    swap₃ l = l

  colimBagChain : Type₂
  colimBagChain = colim (asDiag bagChain)

colim-Bool : Type₂
colim-Bool = colimBagChain Bool

l-tf : colim-Bool
l-tf = colim-leg 3 (cons true (cons false nil))

l-ft : colim-Bool
l-ft = colim-leg 3 (cons false (cons true nil))

tf≡ft : l-tf ≡ l-ft
tf≡ft = colim-com onlyIdx ≡$ (cons false (cons true nil))

l-ttf : colim-Bool
l-ttf = colim-leg 4 (cons true (cons true (cons false nil)))

l-tft : colim-Bool
l-tft = colim-leg 4 (cons true (cons false (cons true nil)))

ttf≢tft : ¬ l-ttf ≡ l-tft
ttf≢tft path = false≢true false≡true
  where
  false≡true : false ≡ true
  false≡true = sym d2t1-ttf≡f ∙ cong drop2-take1 path ∙ d2t1-tft≡t
    where
    drop2-take1 : colim-Bool → Bool
    drop2-take1 = rec cocone
      where
      cocone : Cocone ℓ-zero (LoopyChain.asDiag (bagChain Bool)) Bool
      cocone .leg (suc (suc (suc (suc n)))) list with list
      ... | cons _ (cons _ (cons b _)) = b
      ... | _ = true
      cocone .leg _ _ = true
      cocone .com {j = m} {k = n} e with areAdj m n
      ... | yes (same .m) = {!   !}
      cocone .com {j = .zero} {k = .1} e | yes (next zero) = {!   !}
      cocone .com {j = .(suc m)} {k = .(suc (suc m))} e | yes (next (suc m)) = {!   !}
    d2t1-ttf≡f : drop2-take1 l-ttf ≡ false
    d2t1-ttf≡f = refl
    d2t1-tft≡t : drop2-take1 l-tft ≡ true
    d2t1-tft≡t = refl
{-   where
  drop1-take2 : colim-Bool → Bool × Bool
  drop1-take2 (colim-leg (suc (suc (suc (suc n)))) l) = drop1-take2' l
    where
    drop1-take2' : ListEndo^ Bool (suc (suc (suc (suc n)))) .Endofunctor.F ⊥ → Bool × Bool
    drop1-take2' nil = true , true
    drop1-take2' (cons a nil) = true , true
    drop1-take2' (cons a (cons a₁ nil)) = true , true
    drop1-take2' (cons a (cons a₁ (cons a₂ _))) = a₁ , a₂
  drop1-take2 (colim-leg n l) = true , true
  drop1-take2 (colim-com {j = m} {k = n} f i a) with areAdj Bool m n
  drop1-take2 (colim-com {j = .3} {k = .3} onlyIdx _ _) | yes (same .3) = true , true
  drop1-take2 (colim-com {j = m} {k = .(suc m)} tt i list-m) | yes (next .m) with m
  ... | suc zero = true , true
  ... | suc (suc zero) = true , true
  ... | suc (suc (suc m')) with list-m
  ... | l' = ? -}
 