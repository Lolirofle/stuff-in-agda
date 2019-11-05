module Type.Cubical.Path.Proofs where

import      Lvl
open import Type
open import Type.Cubical
open import Type.Cubical.Path

module _ where
  private variable ℓ : Lvl.Level
  private variable A B : Type{ℓ}
  private variable P : Interval → Type{ℓ}

  Path-intro : ∀{p : Interval → A} → Path(p(Interval.𝟎)) (p(Interval.𝟏))
  Path-intro {p = p} i = p i

  Path-apply : ∀{x y : A} → Path x y → (Interval → A)
  Path-apply path(i) = path(i)

  -- The path from a point to itself.
  -- This path only consists of x, the point itself.
  constant-path : ∀{x : A} → Path x x
  constant-path{x = x} _ = x

  -- The reversed path of a path.
  -- Reverses the direction of a path by flipping all points around the point of symmetry.
  reverse-pathp : ∀{x}{y} → PathP(P) x y → PathP(\i → P(Interval.flip i)) y x
  reverse-pathp path(i) = path(Interval.flip i)

  reverse-path : ∀{x y : A} → Path x y → Path y x
  reverse-path = reverse-pathp

  Path-to-[→] : Path A B → (A → B)
  Path-to-[→] path a = {!Interval.transp (test path)!}

  compose-paths : ∀{x y z : A} → Path x y → Path y z → Path x z
  compose-paths {x}{y}{z} xy yz i = {!!}

module _ where
  private variable ℓ₁ : Lvl.Level
  private variable ℓ₂ : Lvl.Level
  private variable X : Type{ℓ₁}
  private variable Y : X → Type{ℓ₂}

  -- Maps a path into another space.
  map-pathp : (f : (x : X) → Y(x)) → ∀{x y : X} → (path : Path x y) → PathP(\i → Y(path(i))) (f(x)) (f(y))
  map-pathp(f) path(i) = f(path(i))

  function-path : ∀{f g : (x : X) → Y(x)} → (∀{x} → Path(f(x)) (g(x))) → Path f g
  function-path paths i x = paths{x} i

module _ where
  private variable ℓ₁ : Lvl.Level
  private variable ℓ₂ : Lvl.Level
  private variable X : Type{ℓ₁}
  private variable Y : Type{ℓ₂}

  map-path : (f : X → Y) → ∀{x y : X} → Path x y → Path (f(x)) (f(y))
  map-path = map-pathp
