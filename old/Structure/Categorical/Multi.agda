module Structure.Categorical.Multi where

open import Data
open import Data.Boolean
open import Data.Tuple using (_⨯_ ; _,_)
open import Data.Tuple.Raiseᵣ
import      Data.Tuple.Raiseᵣ.Functions as Raise
open import Data.Tuple.RaiseTypeᵣ
import      Data.Tuple.RaiseTypeᵣ.Functions as RaiseType
open import Function.Multi
open import Function.Multi.Functions
open import Functional using (_→ᶠ_ ; _on₂_)
import      DependentFunctional as Fn
open import Functional.Instance
import      Lvl
open import Logic
open import Logic.Predicate
open import Logic.Predicate.Multi
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Oper using (_⋅_)
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Relation
open import Structure.Setoid
import      Structure.Categorical.Names as Names
import      Structure.Operator.Names as Names
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Syntax.Function
open import Type
open import Type.Properties.Singleton

private variable ℓ ℓₒ ℓₘ ℓₘ₁ ℓₘ₂ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable Obj Obj₁ Obj₂ : Type{ℓₒ}

module Morphism where
  module _
    (_⟶_ : Obj → Obj → Stmt{ℓₘ})
    ⦃ morphism-equiv : ∀{x y} → Equiv{ℓₑ}(x ⟶ y) ⦄
    where

    {-
    -- Examples:
    --   MorphismChain(3) T x y z
    --   = compose(1) ((x ⟶ y) ,_) (MorphismChain(2) T y) z
    --   = (x ⟶ y) , (MorphismChain(2) T y z)
    --   = (x ⟶ y) , (y ⟶ z) , T(z)
    --
    --   MorphismChain(4) T x y z w
    --   = compose(2) ((x ⟶ y) ,_) (MorphismChain(3) T y) z w
    --   = (x ⟶ y) , (MorphismChain(3) T y z w)
    --   = (x ⟶ y) , (y ⟶ z) , (z ⟶ w) , T(w)
    MorphismChain : (n : ℕ) → (Obj → Type{ℓₘ}) → (RaiseType.repeat (𝐒(n)) Obj) ⇉ Types(Raise.repeat (𝐒(n)) ℓₘ)
    MorphismChain 0         T x   = T(x)
    MorphismChain 1         T x y = (x ⟶ y) , T(y)
    MorphismChain (𝐒(𝐒(n))) T x y = compose(𝐒(n)) ((x ⟶ y) ,_) (MorphismChain(𝐒(n)) T y)

    -- Examples:
    --   MorphismMapping(2) x y
    --   = MorphismChain(2)(x ⟶_) x y
    --   = (x ⟶ y) → (x ⟶ y)
    --
    --   MorphismMapping(3) x y z
    --   = MorphismChain(3)(x ⟶_) x y z
    --   = (x ⟶ y) → (y ⟶ z) → (x ⟶ z)
    --
    --   MorphismMapping(4) x y z w
    --   = MorphismChain(4)(x ⟶_) x y z w
    --   = (x ⟶ y) → (y ⟶ z) → (z ⟶ w) → (x ⟶ w)
    MorphismMapping : (n : ℕ) → (RaiseType.repeat n Obj) ⇉ Type{ℓₘ}
    MorphismMapping(0)   = Unit
    MorphismMapping(1)      = {!!}
    MorphismMapping(𝐒(𝐒 n)) = {!!}
    --MorphismMapping(𝐒 n) = curry(n) {!Fs ↦ (uncurry(n) (MorphismChain(n)) Fs ⇉ (? → ?))!}
    {-
    MorphismMapping(1)       x   = ? -- MorphismChain(1)(x ⟶_) x
    MorphismMapping(𝐒(𝐒(n))) x   = compose(𝐒(n)) (RaiseType.reduceᵣ{𝐒(n)}{\ℓ₁ ℓ₂ → ℓ₁ Lvl.⊔ ℓ₂} _→ᶠ_) (MorphismChain(𝐒(𝐒(n))) (x ⟶_) x)
    -- MorphismChain(𝐒(𝐒(n)))(x ⟶_) x-}
    -}

    {-
    -- TODO: Not sure if every morphism list should look like a chain
    MorphismChain : (n : ℕ) → ⦃ Positive(n) ⦄ → (RaiseType.repeat n Obj) ⇉ Type{ℓₘ}
    MorphismChain 1           x   = x ⟶ x
    MorphismChain 2           x y = x ⟶ y
    MorphismChain (𝐒(𝐒(𝐒(n)))) x y = compose(𝐒(n)) ((x ⟶ y) →ᶠ_) (MorphismChain (𝐒(𝐒(n))) y)

    MorphismFlippedChain : (n : ℕ) → (RaiseType.repeat (𝐒(n)) Obj) ⇉ Type{ℓₘ}
    MorphismFlippedChain 𝟎      x = x ⟶ x
    MorphismFlippedChain (𝐒(n)) x = Out(𝐒(n)) (x ⟶_) x where
      Out : (n : ℕ) → (Obj → Type{ℓₘ}) → (RaiseType.repeat (𝐒(n)) Obj) ⇉ Type{ℓₘ}
      Out 0         T x   = T(x)
      Out 1         T x y = (x ⟶ y) → T(y)
      Out (𝐒(𝐒(n))) T x y = Out(𝐒(n)) (z ↦ ((x ⟶ y) → T(z))) y
    -}

    {-
    MorphismsFromPairs : (n : ℕ) → (RaiseType.repeat(n ⋅ 2) Obj) ⇉ Type{ℓₘ}
    MorphismsFromPairs 0             = Unit
    MorphismsFromPairs 1         x y = x ⟶ y
    MorphismsFromPairs (𝐒(𝐒(n))) x y = compose(𝐒(n) ⋅ 2) ((x ⟶ y) →ᶠ_) (MorphismsFromPairs (𝐒(n)))
    -}

    MorphismsFromPairs : (n : ℕ) → (Obj ^ (n ⋅ 2)) → Type{ℓₘ}
    MorphismsFromPairs 0         <>          = Unit
    MorphismsFromPairs 1         (x , y)     = x ⟶ y
    MorphismsFromPairs (𝐒(𝐒(n))) (x , y , t) = (x ⟶ y) → MorphismsFromPairs (𝐒(n)) t

  module _ 
    (_⟶₁_ : Obj₁ → Obj₁ → Stmt{ℓₘ₁})
    ⦃ morphism-equiv₁ : ∀{x y} → Equiv{ℓₑ₁}(x ⟶₁ y) ⦄
    (_⟶₂_ : Obj₂ → Obj₂ → Stmt{ℓₘ₂})
    ⦃ morphism-equiv₂ : ∀{x y} → Equiv{ℓₑ₂}(x ⟶₂ y) ⦄
    where

    private open module Equiv₂{x}{y} = Equiv(morphism-equiv₂{x}{y}) using () renaming (_≡_ to _≡₂_)

    module _
      {F : Obj₁ → Obj₂}
      where

      test : (n : ℕ) → ∀{ℓ₁ ℓ₂}{ℓ𝓈 : Lvl.Level ^ n}{As : Types(ℓ𝓈)}{P : Type{ℓ₁}}{Q : As ⇉ Type{ℓ₂}} → ∀₊(n) (compose(n) (P →ᶠ_) Q) → (P → ∀₊(n) Q)
      test 0        apq      = apq
      test 1        apq p{x} = apq{x} p
      test (𝐒(𝐒 n)) apq p{x} = test (𝐒 n) (apq{x}) p

      Preserving : (n : ℕ) → {Objs₁ : Obj₁ ^ (𝐒(n) ⋅ 2)} → (∀{x y} → (x ⟶₁ y) → (F(x) ⟶₂ F(y))) → (MorphismsFromPairs(_⟶₁_)(𝐒(n)) Objs₁) → (MorphismsFromPairs(_⟶₂_ on₂ F)(𝐒(n)) Objs₁) → Stmt{if(n ≤? 0) then (ℓₑ₂) else (ℓₘ₁ Lvl.⊔ ℓₑ₂)}
      Preserving 0        {x , y}     map G₁ G₂ = map(G₁) ≡ G₂
      Preserving 1        {x , y , o} map G₁ G₂ = ∀{f : x ⟶₁ y} → map(G₁ f) ≡ G₂(map f)
      Preserving(𝐒(𝐒(n))) {x , y , o} map G₁ G₂ = ∀{f : x ⟶₁ y} → Preserving(𝐒(n)) {o} map (G₁ f) (G₂(map f))

  module _ 
    (_⟶₁_ : Obj₁ → Obj₁ → Stmt{ℓₘ₁})
    ⦃ morphism-equiv₁ : ∀{x y} → Equiv{ℓₑ₁}(x ⟶₁ y) ⦄
    (_⟶₂_ : Obj₂ → Obj₂ → Stmt{ℓₘ₂})
    ⦃ morphism-equiv₂ : ∀{x y} → Equiv{ℓₑ₂}(x ⟶₂ y) ⦄
    where

    postulate _∘₁_ : ∀{x y z} → (y ⟶₁ z) → (x ⟶₁ y) → (x ⟶₁ z)
    postulate _∘₂_ : ∀{x y z} → (y ⟶₂ z) → (x ⟶₂ y) → (x ⟶₂ z)

    test2 = ∀{x y z} → Preserving(_⟶₁_)(_⟶₂_) 2 {y , z , x , y , x , z} {!!} (_∘₁_)(_∘₂_)

      {-
      PreservingFlipped : (n : ℕ) → (∀{x y} → (x ⟶₁ y) → (F(x) ⟶₂ F(y))) → (∀₊(𝐒(n)) (MorphismChain(_⟶₁_)(𝐒(n)))) → (∀₊(𝐒(n)) (MorphismChain(_⟶₂_)(𝐒(n)))) → (RaiseType.repeat (𝐒(n)) Obj₁) ⇉ Stmt{if(n ≤? 1) then (ℓₑ₂) else (ℓₘ₁ Lvl.⊔ ℓₑ₂)}
      PreservingFlipped 0         f g₁ g₂ x   = f{x}{x}(g₁) ≡ g₂
      PreservingFlipped 1         f g₁ g₂ x y = f{x}{y}(g₁) ≡ g₂
      PreservingFlipped 3         f g₁ g₂ x y z w = {!MorphismChain(_⟶₁_) 4 x y z w!} -- ∀{h : y ⟶₁ x} → f{x}{y} (g₁{y}{x} h) ≡ g₂{F y}{F x} (f{y}{x} h)
      PreservingFlipped (𝐒(𝐒(n))) f g₁ g₂ x y = {!t!} where
        t : (∀{z} → (x ⟶₁ z)) → (∀{Fz} → (F(x) ⟶₂ Fz)) → RaiseType.repeat (𝐒(n)) Obj₁ ⇉ Type
        t xz FxFz = PreservingFlipped (𝐒(n)) f (\{z} → test(𝐒(n)) (g₁{x}{z}) xz) (\{Fz} → test(𝐒(n)) (g₂{F(x)}{Fz}) FxFz) y

        {-compose(𝐒(n)) {As = RaiseType.repeat (𝐒 n) Obj₁}{B = (x ⟶₁ y) →  ∀₊ (𝐒 (𝐒 n)) (MorphismChain _⟶₁_ (𝐒 (𝐒 n))) → ∀₊ (𝐒 (𝐒 n)) (MorphismChain _⟶₂_ (𝐒 (𝐒 n))) → Obj₁ → Type{{!!}}}{C = Type}
        (\P → ∀{f : x ⟶₁ y} → P f (\{z} → test(𝐒(n)) (G₁{x}{z}) {!!}) (\{Fz} → test(𝐒(n)) (G₂{F(x)}{Fz}) {!!}) y)
        {!PreservingFlipped (𝐒(n)) map!}-}
      -- (\P → ∀{y}{f : x ⟶₁ y} → P f)
      -- (PreservingFlipped (𝐒(n)) map (\{z} → test(𝐒(n)) (G₁{y}{z}) {!!}) (\{Fz} → test(𝐒(n)) (G₂{F(y)}{Fz}) {!!}) y)

      {-
      -- TODO: _⇉_ has to be dependent so the objects can be applied to P, therefore _⇉d_. But is this not essentially the same as ∀₊ but with explicit params?
      import Lvl.MultiFunctions as Lvl
      _⇉d_ : ∀{n : ℕ}{ℓ}{ℓ𝓈 : Lvl.Level ^ n} → (As : Types(ℓ𝓈)) → (As ⇉ Type{ℓ}) → Type{ℓ Lvl.⊔ (Lvl.⨆ ℓ𝓈)}
      _⇉d_ {0}      <>       B = B
      _⇉d_ {1}      A        B = (a : A) → B(a)
      _⇉d_ {𝐒(𝐒 n)} (A , As) B = (a : A) → As ⇉d B(a)
      [∀₊]-elim : (n : ℕ) → ∀{ℓ}{ℓ𝓈 : Lvl.Level ^ n}{As : Types(ℓ𝓈)}{P : As ⇉ Type{ℓ}} → ∀₊(n) P → (As ⇉d P)
      [∀₊]-elim 0        p   = p
      [∀₊]-elim 1        p a = p{a}
      [∀₊]-elim (𝐒(𝐒 n)) p a = [∀₊]-elim (𝐒 n) (p{a})
      -}
      -}

      {-
      -- Definition of the relation between a function and an operation that says:
      -- The function preserves the operation.
      -- Often used when defining homomorphisms.
      -- Examples:
      --   Preserving(0) (map)(G₁)(G₂)
      --   = ∀{x} → (map ∘₀ G₁ ≡ G₂ on₀ map)
      --   = ∀{x} → (map(G₁) ≡ G₂(f))
      --   Preserving(1) (map)(G₁)(G₂)
      --   = ∀{x y}{f : x ⟶ y} → ((map ∘₁ G₁)(f) ≡ (G₂ on₁ map)(f))
      --   = ∀{x y}{f : x ⟶ y} → (map(G₁(f)) ≡ G₂(map(f)))
      --   Preserving(2) (map)(G₁)(G₂)
      --   = ∀{x y z}{f₁ : y ⟶ z}{f₂ : x ⟶ y} → ((map ∘₂ G₁)(f₁)(f₂) ≡ (G₂ on₂ map)(f₁)(f₂))
      --   = ∀{x y z}{f₁ : y ⟶ z}{f₂ : x ⟶ y} → (map(G₁ f₁ f₂) ≡ G₂ (map(f₁)) (map(f₂)))
      --   Preserving(3) (map)(G₁)(G₂)
      --   = ∀{f₁ f₂ f₃} → ((map ∘₃ G₁)(f₁)(f₂)(f₃) ≡ (G₂ on₃ map)(f₁)(f₂)(f₃))
      --   = ∀{f₁ f₂ f₃} → (map(G₁ f₁ f₂ f₃) ≡ G₂ (map(f₁)) (map(f₂)) (map(f₃)))
      Preserving : (n : ℕ) → (map : ∀{x y} → (x ⟶₁ y) → (F(x) ⟶₂ F(y))) → (∀₊(𝐒(n)) (MorphismFlippedChain(_⟶₁_)(n))) → (∀₊(𝐒(n)) (MorphismFlippedChain(_⟶₂_)(n))) → (RaiseType.repeat (𝐒(n)) Obj₁) ⇉ Stmt{if(n ≤? 0) then (ℓₑ₂) else (ℓₘ₁ Lvl.⊔ ℓₑ₂)}
      Preserving 0            map G₁ G₂ x     = (map{x}(G₁) ≡ G₂)
      Preserving 1            map G₁ G₂ x y   = ∀{f : x ⟶₁ y} → map(G₁(f)) ≡ G₂(map f)
      Preserving (𝐒(𝐒(n)))    map G₁ G₂ x y   = compose(𝐒(n)) {As = RaiseType.repeat (𝐒 n) Obj₁}{B = (x ⟶₁ y) → Type{ℓₘ₁ Lvl.⊔ ℓₑ₂}}{C = Type}
        (\P → ∀{f : x ⟶₁ y} → P f)
        {!!} -- TODO: There are a number of problems here. First, the f have to be reached somehow so P should probably not receive the f immediately. Maybe (\P → ∀{f : x ⟶₁ y} → P(G₁(f)) (G₂(map f))) or something that applies f. Second, G₁ and G₂ are not applicable because they are not functions. This could be caused by MorphismFlippedChain being in reverse so there is no term extracted (it is folding to the left: [∀₊]-elim (𝐒(𝐒 n)) p a = [∀₊]-elim (𝐒 n) (p{a}), so only in the end, any terms will be accessible). An alternative would be to apply it manually, but the challenge would then be to eliminate a ∀₊ quantifier. Implemented a [∀₊]-elim above but it results in a (As ⇉d P) term and not (As ⇉ P) as needed. So, maybe it is easier to implement a Preserving in the normal direction instead: ∀{x y z}{f₁ : x ⟶ y}{f₂ : y ⟶ z} instead of ∀{x y z}{f₁ : y ⟶ z}{f₂ : x ⟶ y}
        -- G₁{x}{y}
      -- Preserving(𝐒(n)) map ? ? y
      -- ∀{f} → (G₁(f)) (G₂(map f))
      --Preserving 2            map G₁ G₂ x y z = ∀{f₁ : y ⟶₁ z}{f₂ : x ⟶₁ y} → (map(G₁(f₁)(f₂)) ≡ G₂(map f₁)(map f₂))
      -- Preserving (𝐒(𝐒(𝐒(n)))) map G₁ G₂ x y z = {!∀{f} → Preserving(𝐒(𝐒(n))) map !}
      --test (P ↦ (∀{f} → P f)) (f ↦ Preserving (𝐒(𝐒(n))) map {!G₁!} {!G₂!} y z) where
      --  test : ((P : {!!}) → TYPE ({!!} Lvl.⊔ {!!})) → ((f : {!!} ⟶₁ {!!}) → RaiseType.repeat (𝐒 n) Obj₁ ⇉ Type) → (RaiseType.repeat (𝐒 n) Obj₁ ⇉ Type)
        -- compose(𝐒(n)) (P ↦ (∀{f} → P f)) ({!f ↦ Preserving (𝐒(𝐒(n))) map {!G₁!} {!G₂!} {!!} {!!}!})
      -- compose(𝐒(n)) {!!} {!!}
      -- ∀{f : x ⟶₁ y} → 
      -- Preserving(𝐒(𝐒(n))) map (\{a b} → {!G₁{a}{x}{b}!}) \{a b} → {!G₂{a}{F x}{b}!}
    -}

{-
-- Preserving 3 map G₁ G₂ a x y z
-- = ∀{f : a ⟶₁ x} → Preserving 2 map (G₁(f)) (G₂(map f)) x y z
-- = ∀{f : a ⟶₁ x}{f₁ : x ⟶₁ y}{f₂ : y ⟶₁ z} → (map(G₁(f)(f₁)(f₂)) ≡ G₂(map f)(map f₁)(map f₂))


      -- ∀{x y}{f : x ⟶₁ y} → Preserving(𝐒(𝐒(n))) (map) (G₁(f)) (G₂(map(f)))
{-      Preserving(𝟎)       (f)(g₁)(g₂) = (f(g₁) ≡ g₂)
      Preserving(𝐒(𝟎))    (f)(g₁)(g₂) = (∀{x} → f(g₁(x)) ≡ g₂(f(x)))
      Preserving(𝐒(𝐒(n))) (f)(g₁)(g₂) = (∀{x} → Preserving(𝐒(n)) (f) (g₁(x)) (g₂(f(x))))
  -- ∀{x y z : Objₗ}{f : y ⟶ z}{g : x ⟶ y} → (map(f ∘ g) ≡ map(f) ∘ map(g))
-}

-}
