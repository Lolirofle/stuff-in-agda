{-# OPTIONS --cubical #-}

module Type.Cubical.InductivePath where

open import Functional
import      Lvl
open import Type
import      Type.Cubical as Cubical
open import Type.Cubical.InductiveInterval

private variable ℓ : Lvl.Level
private variable A B P : Type{ℓ}
private variable x y z : A

data Path {P : Type{ℓ}} : P → P → Type{ℓ} where
  intro : (p : Interval → P) → Path(p(𝟎)) (p(𝟏))

point : (x : P) → Path x x
point x = intro(const x)

pointOn : ∀{x y : A} → Path x y → (Interval → A)
pointOn (intro p) = p

reverse : Path x y → Path y x
reverse(intro f) = intro(f ∘ flip)

spaceMap : Path A B → (A → B)
spaceMap (intro p) = transp p

{-
concat : Path x y → Path y z → Path x z
concat xy yz = {!xy yz!}
-}

module _ where
  private variable X : Type{ℓ}
  private variable Y : X → Type{ℓ}

  {- TODO: Define an eliminator for Path and use it to prove this?
  mapping : ∀{f g : (x : X) → Y(x)} → (∀{x} → Path(f(x)) (g(x))) → Path f g
  mapping {X = X}{Y = Y}{f = f}{g = g} ppt = intro(i ↦ x ↦ {!pointOn(ppt{x}) i!}) where
    p : (∀{x} → Path(f(x)) (g(x))) → Interval → (x : X) → Y(x)
    p ppt i x with ppt{x}
    ... | q = {!q!}
  -}
  
  mappingPoint : ∀{f g : (x : X) → Y(x)} → Path f g → (∀{x} → Path(f(x)) (g(x)))
  mappingPoint (intro pfg) {x} = intro (i ↦ pfg i x)

module _ where
  private variable X X₁ X₂ Y Y₁ Y₂ : Type{ℓ}

  map : (f : X → Y) → ∀{a b} → Path a b → Path (f(a)) (f(b))
  map f (intro ab) = intro(f ∘ ab)

  liftedSpaceMap : (S : X → Type{ℓ}) → ∀{a b} → Path a b → S(a) → S(b)
  liftedSpaceMap S p = spaceMap(map S p)
