module Type.Cubical.Path.Proofs where

import      Lvl
open import Type
open import Type.Cubical
open import Type.Cubical.Path

module _ where
  private variable ℓ₁ : Lvl.Level
  private variable A : Type{ℓ₁}
  private variable P : Interval → Type{ℓ₁}

  -- The path from a point to itself.
  -- This path only consists of x, the point itself.
  constant-path : ∀{x : A} → Path x x
  constant-path{x = x} _ = x

  -- The reversed path of a path.
  -- Reverses the direction of a path by flipping all points around the point of symmetry.
  reversed-pathp : ∀{x}{y} → PathP(P) x y → PathP(\i → P(Interval.inv i)) y x
  reversed-pathp path(i) = path(Interval.inv i)

  reversed-path : ∀{x y : A} → Path x y → Path y x
  reversed-path = reversed-pathp

module _ where
  private variable ℓ₁ : Lvl.Level
  private variable ℓ₂ : Lvl.Level
  private variable X : Type{ℓ₁}
  private variable Y : X → Type{ℓ₂}

  -- Maps a path into another space.
  map-path : (f : (x : X) → Y(x)) → ∀{x y : X} → (path : Path x y) → PathP(\i → Y(path(i))) (f(x)) (f(y))
  map-path(f) path(i) = f(path(i))

-- compose-paths : ∀{P : Type{ℓ}}{x : P}{y : P} → Path x y → Path y z → Path x z
-- compose-paths{P}{x} path(i) = path(Interval.inv i)

module _ where
  private variable ℓ₁ : Lvl.Level
  private variable ℓ₂ : Lvl.Level
  private variable X : Type{ℓ₁}
  private variable Y : X → Type{ℓ₂}

  function-path : ∀{f g : (x : X) → Y(x)} → (∀{x} → Path(f(x)) (g(x))) → Path f g
  function-path paths i x = paths{x} i
