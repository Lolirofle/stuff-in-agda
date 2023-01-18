module Signature.Algebraic where

-- TODO: Not really what I had in mind. Rewrite or remove this module

open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional as Fn using (_←_ ; _→ᶠ_)
import      Lvl
open import Type

record Monoid : Typeω where
  constructor monoid
  field
    {ℓ} : Lvl.Level
    T : Type{ℓ}
    _▫_ : T → T → T
    id  : T

record Group : Typeω where
  constructor group
  field
    {ℓ} : Lvl.Level
    T : Type{ℓ}
    _▫_ : T → T → T
    inv : T → T
    id  : T

record Category : Typeω where
  constructor category
  field
    {ℓₒ} : Lvl.Level
    {ℓₘ} : Lvl.Level
    Obj : Type{ℓₒ}
    _⟶_ : Obj → Obj → Type{ℓₘ}
    _∘_ : ∀{a b c} → (b ⟶ c) → (a ⟶ b) → (a ⟶ c)
    id  : ∀{a} → (a ⟶ a)

oppᶜᵃᵗ : Category → Category
oppᶜᵃᵗ a = category Obj (Fn.swap(_⟶_)) (Fn.swap(_∘_)) id where open Category a

_⨯ᶜᵃᵗ_ : Category → Category → Category
a ⨯ᶜᵃᵗ b =
  let open Category(a) using () renaming (Obj to Objₗ ; _⟶_ to _⟶ₗ_ ; _∘_ to _∘ₗ_ ; id to idₗ)
      open Category(b) using () renaming (Obj to Objᵣ ; _⟶_ to _⟶ᵣ_ ; _∘_ to _∘ᵣ_ ; id to idᵣ)
  in category
    (Objₗ ⨯ Objᵣ)
    (Tuple.uncurry(_⨯_) Fn.∘₂ Tuple.map₂(_⟶ₗ_)(_⟶ᵣ_))
    (Tuple.map₂(_∘ₗ_)(_∘ᵣ_))
    (idₗ , idᵣ)

record Functor (Cₗ : Category) (Cᵣ : Category) : Type{Category.ℓₒ Cₗ Lvl.⊔ Category.ℓₒ Cᵣ Lvl.⊔ Category.ℓₘ Cₗ Lvl.⊔ Category.ℓₘ Cᵣ} where
  constructor functor
  open Category(Cₗ) using () renaming (Obj to Objₗ ; _⟶_ to _⟶ₗ_)
  open Category(Cᵣ) using () renaming (Obj to Objᵣ ; _⟶_ to _⟶ᵣ_)
  field
    mapₒ : Objₗ → Objᵣ
    mapₘ : ∀{a b} → (a ⟶ₗ b) → (mapₒ(a) ⟶ᵣ mapₒ(b))
_→ᶠᵘⁿᶜᵗᵒʳ_ = Functor

Endofunctor = \C → C →ᶠᵘⁿᶜᵗᵒʳ C

_→ᴺᵀ_ : ∀{Cₗ Cᵣ} → (Cₗ →ᶠᵘⁿᶜᵗᵒʳ Cᵣ) → (Cₗ →ᶠᵘⁿᶜᵗᵒʳ Cᵣ) → Type
_→ᴺᵀ_ {Cₗ}{Cᵣ} F₁ F₂ =
  let _⟶_ = Category._⟶_ Cᵣ
      F   = Functor.mapₒ F₁
      G   = Functor.mapₒ F₂
  in ∀{x} → (F(x) ⟶ G(x))

_↔ᴺᵀ_ : ∀{Cₗ Cᵣ} → (Cₗ →ᶠᵘⁿᶜᵗᵒʳ Cᵣ) → (Cₗ →ᶠᵘⁿᶜᵗᵒʳ Cᵣ) → Type
F₁ ↔ᴺᵀ F₂ = (F₂ →ᴺᵀ F₁) ⨯ (F₁ →ᴺᵀ F₂)

idᴺᵀ : ∀{a b}{f : a →ᶠᵘⁿᶜᵗᵒʳ b} → (f →ᴺᵀ f)
idᴺᵀ{a}{b}{f} = Category.id b

_∘ᴺᵀ_ : ∀{a b}{f g h : a →ᶠᵘⁿᶜᵗᵒʳ b} → (g →ᴺᵀ h) → (f →ᴺᵀ g) → (f →ᴺᵀ h)
_∘ᴺᵀ_ {a}{b} {f}{g}{h} F G {x} = Category._∘_ b F G

idᶠᵘⁿᶜᵗᵒʳ : ∀{a} → (a →ᶠᵘⁿᶜᵗᵒʳ a)
idᶠᵘⁿᶜᵗᵒʳ = functor Fn.id Fn.id

_∘ᶠᵘⁿᶜᵗᵒʳ_ : ∀{a b c} → (b →ᶠᵘⁿᶜᵗᵒʳ c) → (a →ᶠᵘⁿᶜᵗᵒʳ b) → (a →ᶠᵘⁿᶜᵗᵒʳ c)
f ∘ᶠᵘⁿᶜᵗᵒʳ g = functor(mapₒ(f) Fn.∘ mapₒ(g)) (mapₘ(f) Fn.∘ mapₘ(g)) where open Functor

constᶠᵘⁿᶜᵗᵒʳ : ∀{a b} → Category.Obj(b) → (a →ᶠᵘⁿᶜᵗᵒʳ b)
constᶠᵘⁿᶜᵗᵒʳ{b = b} c = functor (Fn.const c) (Fn.const(Category.id b))

functorOppSideₗ : ∀{a b} → (oppᶜᵃᵗ(a) →ᶠᵘⁿᶜᵗᵒʳ b) → (a →ᶠᵘⁿᶜᵗᵒʳ oppᶜᵃᵗ(b))
functorOppSideₗ(functor o i) = functor o i

functorOppSideᵣ : ∀{a b} → (a →ᶠᵘⁿᶜᵗᵒʳ oppᶜᵃᵗ(b)) → (oppᶜᵃᵗ(a) →ᶠᵘⁿᶜᵗᵒʳ b)
functorOppSideᵣ(functor o i) = functor o i

-- TODO: This is a functor in the category category.
oppᶜᵃᵗ-functor : ∀{a b} → (a →ᶠᵘⁿᶜᵗᵒʳ b) → (oppᶜᵃᵗ(a) →ᶠᵘⁿᶜᵗᵒʳ oppᶜᵃᵗ(b))
oppᶜᵃᵗ-functor (functor o i) = functor o i

functorCategory : Category → Category → Category
functorCategory a b = category (a →ᶠᵘⁿᶜᵗᵒʳ b) (_→ᴺᵀ_) (\{f}{g}{h} → _∘ᴺᵀ_ {f = f}{g = g}{h = h}) (\{f} → idᴺᵀ{f = f})

module Tupleᶜᵃᵗ where
  map : ∀{a₁ b₁ a₂ b₂} → (a₁ →ᶠᵘⁿᶜᵗᵒʳ b₁) → (a₂ →ᶠᵘⁿᶜᵗᵒʳ b₂) → ((a₁ ⨯ᶜᵃᵗ a₂) →ᶠᵘⁿᶜᵗᵒʳ (b₁ ⨯ᶜᵃᵗ b₂))
  map f g = functor (Tuple.map(mapₒ f) (mapₒ g)) (Tuple.map(mapₘ f) (mapₘ g)) where open Functor

  mapLeft : ∀{a b c} → (a →ᶠᵘⁿᶜᵗᵒʳ b) → ((a ⨯ᶜᵃᵗ c) →ᶠᵘⁿᶜᵗᵒʳ (b ⨯ᶜᵃᵗ c))
  mapLeft F = map F idᶠᵘⁿᶜᵗᵒʳ

  mapRight : ∀{a b c} → (b →ᶠᵘⁿᶜᵗᵒʳ c) → ((a ⨯ᶜᵃᵗ b) →ᶠᵘⁿᶜᵗᵒʳ (a ⨯ᶜᵃᵗ c))
  mapRight F = map idᶠᵘⁿᶜᵗᵒʳ F

  left : ∀{a b} → ((a ⨯ᶜᵃᵗ b) →ᶠᵘⁿᶜᵗᵒʳ a)
  left = functor Tuple.left Tuple.left

  right : ∀{a b} → ((a ⨯ᶜᵃᵗ b) →ᶠᵘⁿᶜᵗᵒʳ b)
  right = functor Tuple.right Tuple.right

  diag : ∀{a} → (a →ᶠᵘⁿᶜᵗᵒʳ (a ⨯ᶜᵃᵗ a))
  diag = functor Tuple.diag Tuple.diag

  constₗ : ∀{a b} → Category.Obj(a) → (b →ᶠᵘⁿᶜᵗᵒʳ (a ⨯ᶜᵃᵗ b))
  constₗ c = mapLeft(constᶠᵘⁿᶜᵗᵒʳ c) ∘ᶠᵘⁿᶜᵗᵒʳ diag

  constᵣ : ∀{a b} → Category.Obj(b) → (a →ᶠᵘⁿᶜᵗᵒʳ (a ⨯ᶜᵃᵗ b))
  constᵣ c = mapRight(constᶠᵘⁿᶜᵗᵒʳ c) ∘ᶠᵘⁿᶜᵗᵒʳ diag

  applyₗ : ∀{a b c} → Category.Obj(a) → ((a ⨯ᶜᵃᵗ b) →ᶠᵘⁿᶜᵗᵒʳ c) → (b →ᶠᵘⁿᶜᵗᵒʳ c)
  applyₗ x = _∘ᶠᵘⁿᶜᵗᵒʳ (constₗ x)

  applyᵣ : ∀{a b c} → Category.Obj(b) → ((a ⨯ᶜᵃᵗ b) →ᶠᵘⁿᶜᵗᵒʳ c) → (a →ᶠᵘⁿᶜᵗᵒʳ c)
  applyᵣ x = _∘ᶠᵘⁿᶜᵗᵒʳ (constᵣ x)

record Monad (C : Category) : Typeω where
  constructor monad
  field
    T : Endofunctor(C)
    join : (T ∘ᶠᵘⁿᶜᵗᵒʳ T) →ᴺᵀ T
    lift : idᶠᵘⁿᶜᵗᵒʳ →ᴺᵀ T

record MonoidalCategory : Typeω where
  constructor monoidalCategory
  field C : Category
  open Category(C) public
  field
    product : (C ⨯ᶜᵃᵗ C) →ᶠᵘⁿᶜᵗᵒʳ C
    𝟏 : Obj
  
  _⊗_ : Obj → Obj → Obj
  _⊗_ = Tuple.curry(Functor.mapₒ product)

  _<⊗>_ : ∀{x₁ x₂ y₁ y₂} → (x₁ ⟶ x₂) → (y₁ ⟶ y₂) → ((x₁ ⊗ y₁) ⟶ (x₂ ⊗ y₂))
  _<⊗>_ = Tuple.curry(Functor.mapₘ product)

record MonoidalFunctor (Mₗ : MonoidalCategory) (Mᵣ : MonoidalCategory) : Typeω where
  constructor monoidalFunctor
  open MonoidalCategory(Mₗ) using () renaming (C to Cₗ ; Obj to Objₗ ; _⟶_ to _⟶ₗ_ ; product to Pₗ ; 𝟏 to 𝟏ₗ)
  open MonoidalCategory(Mᵣ) using () renaming (C to Cᵣ ; Obj to Objᵣ ; _⟶_ to _⟶ᵣ_ ; product to Pᵣ ; 𝟏 to 𝟏ᵣ)
  field F : Cₗ →ᶠᵘⁿᶜᵗᵒʳ Cᵣ
  open Functor(F) public
  field
    map⊗ : (Pᵣ ∘ᶠᵘⁿᶜᵗᵒʳ Tupleᶜᵃᵗ.map F F) →ᴺᵀ (F ∘ᶠᵘⁿᶜᵗᵒʳ Pₗ)
    map𝟏 : 𝟏ᵣ ⟶ᵣ mapₒ(𝟏ₗ)
_→ᵐᵒⁿᵒⁱᵈᵃˡᶠᵘⁿᶜᵗᵒʳ_ = MonoidalFunctor

MonoidalEndofunctor = \C → C →ᵐᵒⁿᵒⁱᵈᵃˡᶠᵘⁿᶜᵗᵒʳ C

-- A monoidal functor equipped with a tensorial strength.
record StrongMonoidalFunctor (M : MonoidalCategory) : Typeω where
  constructor strongMonoidalFunctor
  open MonoidalCategory(M) renaming (product to P)
  field MF : MonoidalEndofunctor M
  open MonoidalFunctor(MF) public
  field
    Β : (P ∘ᶠᵘⁿᶜᵗᵒʳ Tupleᶜᵃᵗ.map idᶠᵘⁿᶜᵗᵒʳ F) →ᴺᵀ (F ∘ᶠᵘⁿᶜᵗᵒʳ P)

record ClosedCategory : Typeω where
  constructor closedCategory
  field C : Category
  open Category(C) public
  field
    hom : ((oppᶜᵃᵗ C) ⨯ᶜᵃᵗ C) →ᶠᵘⁿᶜᵗᵒʳ C
    unit : Obj
    -- TODO: Unfinished

  _⊗_ : Obj → Obj → Obj
  _⊗_ = Tuple.curry(Functor.mapₒ hom)

  _<⊗>_ : ∀{x₁ x₂ y₁ y₂} → (x₂ ⟶ x₁) → (y₁ ⟶ y₂) → ((x₁ ⊗ y₁) ⟶ (x₂ ⊗ y₂))
  _<⊗>_ = Tuple.curry(Functor.mapₘ hom)

record Adjunction {Cₗ Cᵣ} (Left : Cᵣ →ᶠᵘⁿᶜᵗᵒʳ Cₗ) (Right : Cₗ →ᶠᵘⁿᶜᵗᵒʳ Cᵣ) : Typeω where
  constructor adjunction
  open Category(Cₗ) using () renaming (Obj to Objₗ ; _⟶_ to _⟶ₗ_)
  open Category(Cᵣ) using () renaming (Obj to Objᵣ ; _⟶_ to _⟶ᵣ_)
  open Functor(Left)  using () renaming (mapₒ to F)
  open Functor(Right) using () renaming (mapₒ to G)
  field
    left  : ∀{a b} → (F(a) ⟶ₗ b) ← (a ⟶ᵣ G(b))
    right : ∀{a b} → (F(a) ⟶ₗ b) → (a ⟶ᵣ G(b))

    unit : idᶠᵘⁿᶜᵗᵒʳ →ᴺᵀ (Right ∘ᶠᵘⁿᶜᵗᵒʳ Left)
    counit : (Left ∘ᶠᵘⁿᶜᵗᵒʳ Right) →ᴺᵀ idᶠᵘⁿᶜᵗᵒʳ

{-
module _
  (M : MonoidalCategory)
  (homᵣ : MonoidalCategory.C(M) →ᶠᵘⁿᶜᵗᵒʳ MonoidalCategory.C(M))
  (curryingAdjunction : ∀{b : Category.Obj(MonoidalCategory.C(M))} → Adjunction(Tupleᶜᵃᵗ.applyᵣ b (MonoidalCategory.product(M))) homᵣ)
  (monoidalFunctor : MonoidalEndofunctor(M))
  where

  open MonoidalCategory(M)
  open MonoidalFunctor(monoidalFunctor)

  lift : idᶠᵘⁿᶜᵗᵒʳ →ᴺᵀ F
  lift{a} = {!!}
  -- {!map𝟏!} ∘ Adjunction.unit(curryingAdjunction{a})
  -- Functor.mapₘ{C}{C} (constᶠᵘⁿᶜᵗᵒʳ a)
  -- map𝟏
  -- Functor.mapₘ F (Fn.const a) (MonoidalFunctor.map𝟏 monoidalFunctor ?)

  -- _<*>_ : ∀{a b : Category.Obj(C)} → mapₒ(a → b) → (mapₒ(a) → mapₒ(b))
  -- f <*> l = Functor.mapₘ F (Tuple.uncurry(Fn._$_)) (MonoidalFunctor.map⊗ monoidalFunctor(f , l))
-}

module _ where
  private variable ℓ ℓ₁ ℓ₂ : Lvl.Level

  typeCategory : {ℓ : Lvl.Level} → Category
  typeCategory{ℓ} = category(Type{ℓ}) (Fn._→ᶠ_) (Fn._∘_) Fn.id

  open import Data

  [⨯]-functor : (typeCategory{ℓ₁} ⨯ᶜᵃᵗ typeCategory{ℓ₂}) →ᶠᵘⁿᶜᵗᵒʳ typeCategory
  [⨯]-functor = functor(Tuple.uncurry(_⨯_)) (Tuple.uncurry Tuple.map)

  typeMonoidalCategory : {ℓ : Lvl.Level} → MonoidalCategory
  typeMonoidalCategory{ℓ} = monoidalCategory(typeCategory{ℓ}) [⨯]-functor Unit

  -- Also called: Hom functor.
  [⟶]-functor : (C : Category) → ((oppᶜᵃᵗ(C) ⨯ᶜᵃᵗ C) →ᶠᵘⁿᶜᵗᵒʳ typeCategory)
  [⟶]-functor C = functor(Tuple.uncurry(_⟶_)) (Tuple.uncurry(\f g h → g ∘ (h ∘ f))) where open Category(C)

  -- typeCategory is a closed monoidal category (have an exponential object).
  curryingAdjunction : ∀{b : Type{ℓ}} → Adjunction(Tupleᶜᵃᵗ.applyᵣ b ([⨯]-functor{ℓ})) (Tupleᶜᵃᵗ.applyₗ b ([⟶]-functor typeCategory))
  curryingAdjunction = adjunction Tuple.uncurry Tuple.curry (_,_) (Tuple.uncurry(Fn._$_))

  swapAdjunction : ∀{b : Type{ℓ}} → Adjunction(functorOppSideᵣ(Tupleᶜᵃᵗ.applyᵣ b ([⟶]-functor typeCategory))) (Tupleᶜᵃᵗ.applyᵣ b ([⟶]-functor typeCategory))
  swapAdjunction = adjunction Fn.swap Fn.swap Fn.apply Fn.apply

  open import Data.List
  import      Data.List.Functions as List

  listFunctor : Endofunctor(typeCategory{ℓ})
  listFunctor = functor List List.map

  listMonoidalFunctor : MonoidalEndofunctor(typeMonoidalCategory{ℓ})
  listMonoidalFunctor = monoidalFunctor listFunctor (Tuple.uncurry(List.map₂(_,_) (Fn.const ∅) (Fn.const ∅))) List.singleton

  listStrongMonoidalFunctor : StrongMonoidalFunctor(typeMonoidalCategory{ℓ})
  listStrongMonoidalFunctor = strongMonoidalFunctor listMonoidalFunctor (Tuple.uncurry(List.map Fn.∘ (_,_)))

  -- <*> : (C : ClosedMonoidalCategory) → (F : MonoidalFunctor C) → ∀{a b} → F(b ^ a) → (F(a) ⟶ F(b))

  liftₗ : idᶠᵘⁿᶜᵗᵒʳ →ᴺᵀ listFunctor{ℓ} -- ∀{a : Type{ℓ}} → a → List(a)
  liftₗ a = Functor.mapₘ listFunctor (Fn.const a) (MonoidalFunctor.map𝟏 listMonoidalFunctor <>)

  _<*>ₗ_ : (listFunctor{Lvl.𝟎} ∘ᶠᵘⁿᶜᵗᵒʳ ([⟶]-functor typeCategory)) →ᴺᵀ (([⟶]-functor typeCategory) ∘ᶠᵘⁿᶜᵗᵒʳ (Tupleᶜᵃᵗ.map (oppᶜᵃᵗ-functor listFunctor) listFunctor)) -- ∀{a b : Type{ℓ}} → List(a → b) → (List(a) → List(b))
  f <*>ₗ l = Functor.mapₘ listFunctor (Tuple.uncurry(Fn._$_)) (MonoidalFunctor.map⊗ listMonoidalFunctor(f , l))
