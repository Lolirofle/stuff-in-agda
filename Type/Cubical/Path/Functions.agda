{-# OPTIONS --cubical #-}

module Type.Cubical.Path.Functions where

open import BidirectionalFunction using (_↔_ ; intro)
import      Lvl
open import Type
open import Type.Cubical
open import Type.Cubical.Path

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level

module _ where
  private variable A B : Type{ℓ}
  private variable P : Interval → Type{ℓ}
  private variable x y z w : A

  -- The full path from the starting point to the end.
  path : (p : (i : Interval) → P(i)) → PathP P (p Interval.𝟎) (p Interval.𝟏)
  path p i = p i
  {-# INLINE path #-}

  -- The point on the path, given a point on the interval indexing the path.
  _$ₚₐₜₕ_ : ∀{x : P(Interval.𝟎)}{y : P(Interval.𝟏)} → PathP P x y → ((i : Interval) → P(i))
  _$ₚₐₜₕ_ p i = p i
  {-# INLINE _$ₚₐₜₕ_ #-}

  applyₚₐₜₕ : ∀{x : P(Interval.𝟎)}{y : P(Interval.𝟏)} → (i : Interval) → PathP P x y → P(i)
  applyₚₐₜₕ i p = p i
  {-# INLINE applyₚₐₜₕ #-}

  -- The path from a point to itself.
  -- This path only consists of the point itself.
  point : Path x x
  point{x = x} _ = x
  {-# INLINE point #-}

  -- The reverse path of a path.
  -- Reverses the direction of a path by flipping all points around the point of symmetry.
  reverseP : PathP(P) x y → PathP(\i → P(Interval.flip i)) y x
  reverseP p(i) = p(Interval.flip i)
  {-# INLINE reverseP #-}

  reverse : Path x y → Path y x
  reverse = reverseP
  {-# INLINE reverse #-}

  -- A function mapping points between two spaces, given a path between the spaces.
  spaceMap : Path A B → (A → B)
  spaceMap p = Interval.transp(p $ₚₐₜₕ_) Interval.𝟎

  -- A function mapping points between two spaces, given a path between the spaces.
  spaceBimap : Path A B → (A ↔ B)
  spaceBimap p = intro (spaceMap(reverse p)) (spaceMap p)

  module _ {A : Type{ℓ}} where
    private variable a₀ a₁ a₂ a₃ : A
    private variable a₀₀ a₀₁ a₁₀ a₁₁ : A
    private variable a₀₀₀ a₀₀₁ a₀₁₀ a₀₁₁ a₁₀₀ a₁₀₁ a₁₁₀ a₁₁₁ : A
    private variable p₀₀₋ p₀₁₋ p₀₋₀ p₀₋₁ p₁₀₋ p₁₁₋ p₁₋₀ p₁₋₁ p₋₀₀ p₋₀₁ p₋₁₀ p₋₁₁ : Path a₀ a₁

    Path-missingSide : A → A
    Path-missingSide a = Interval.hComp diag a where
      diag : Interval → Interval.Partial Interval.𝟎 A
      diag i ()

    module _
      (p₀₋ : Path a₀₀ a₀₁)
      (p₁₋ : Path a₁₀ a₁₁)
      (p₋₀ : Path a₀₀ a₁₀)
      (p₋₁ : Path a₀₁ a₁₁)
      where
      -- a₀₁ → p₋₁ → a₁₁
      --  ↑           ↑
      -- p₀₋         p₁₋
      --  ↑           ↑
      -- a₀₀ → p₋₀ → a₁₀
      Square : Type
      Square = PathP (\i → Path (p₋₀ i) (p₋₁ i)) p₀₋ p₁₋
    module Square where
      missingSide : Path a₀₀ a₀₁ → Path a₁₀ a₁₁ → Path a₀₀ a₁₀ → Path a₀₁ a₁₁
      missingSide p₀₋ p₁₋ p₋₀ ix = Interval.hComp diagram (p₋₀ ix) where
        diagram : Interval → Interval.Partial(Interval.max ix (Interval.flip ix)) A
        diagram iy (ix = Interval.𝟎) = p₀₋ iy
        diagram iy (ix = Interval.𝟏) = p₁₋ iy

      module _
        {p₀₋ : Path a₀₀ a₀₁}
        {p₁₋ : Path a₁₀ a₁₁}
        {p₋₀ : Path a₀₀ a₁₀}
        {p₋₁ : Path a₀₁ a₁₁}
        (s : Square p₀₋ p₁₋ p₋₀ p₋₁)
        where

        diagonal : Path a₀₀ a₁₁
        diagonal i = s i i

        rotate₊ : Square p₋₁ p₋₀ (reverse p₀₋) (reverse p₁₋)
        rotate₊ iy ix = s ix (Interval.flip iy)

        rotate₋ : Square (reverse p₋₀) (reverse p₋₁) p₁₋ p₀₋
        rotate₋ iy ix = s (Interval.flip ix) iy

        flipX : Square p₁₋ p₀₋ (reverse p₋₀) (reverse p₋₁)
        flipX iy ix = s (Interval.flip iy) ix

        flipY : Square (reverse p₀₋) (reverse p₁₋) p₋₁ p₋₀
        flipY iy ix = s iy (Interval.flip ix)

      module _
        {a₀ a₁ : A}
        (p : Path a₀ a₁)
        where

        lineX : Square point point p p
        lineX ix iy = p ix

        lineY : Square p p point point
        lineY ix iy = p iy

        min : Square point p point p
        min ix iy = p(Interval.min ix iy)

        max : Square p point p point
        max ix iy = p(Interval.max ix iy)

    module _
      (p₀₋₋ : Square p₀₀₋ p₀₁₋ p₀₋₀ p₀₋₁)
      (p₁₋₋ : Square p₁₀₋ p₁₁₋ p₁₋₀ p₁₋₁)
      (p₋₀₋ : Square p₀₀₋ p₁₀₋ p₋₀₀ p₋₀₁)
      (p₋₁₋ : Square p₀₁₋ p₁₁₋ p₋₁₀ p₋₁₁)
      (p₋₋₀ : Square p₀₋₀ p₁₋₀ p₋₀₀ p₋₁₀)
      (p₋₋₁ : Square p₀₋₁ p₁₋₁ p₋₀₁ p₋₁₁)
      where

      Cube : Type
      Cube = PathP (\i → Square (p₋₀₋ i) (p₋₁₋ i) (p₋₋₀ i) (p₋₋₁ i)) p₀₋₋ p₁₋₋
    {-
    module Cube where
      module _
        (p₀₋₋ : Square p₀₀₋ p₀₁₋ p₀₋₀ p₀₋₁)
        (p₁₋₋ : Square p₁₀₋ p₁₁₋ p₁₋₀ p₁₋₁)
        (p₋₀₋ : Square p₀₀₋ p₁₀₋ p₋₀₀ p₋₀₁)
        (p₋₁₋ : Square p₀₁₋ p₁₁₋ p₋₁₀ p₋₁₁)
        (p₋₋₀ : Square p₀₋₀ p₁₋₀ p₋₀₀ p₋₁₀)
        where
        missingSide : Square p₀₋₁ p₁₋₁ p₋₀₁ p₋₁₁
        missingSide ix iy = Interval.hComp diagram (p₋₋₀ ix iy) where -- (Square.max {!!} ix iy)
          diagram : Interval → Interval.Partial {!!} A
          {-diagram : (i : Interval) → Interval.Partial (Interval.max (Interval.max ix (Interval.flip ix)) (Interval.max iy (Interval.flip iy))) _
          diagram iz (ix = Interval.𝟎) = Square.max p₀₋₁ ix iy
          diagram iz (ix = Interval.𝟏) = Square.min p₁₋₁ ix iy
          diagram iz (iy = Interval.𝟎) = Square.max p₋₀₁ ix iy
          diagram iz (iy = Interval.𝟏) = Square.min p₋₁₁ ix iy-}
    -}

  -- Concatenates (joins the ends of) two paths.
  concat : Path x y → Path y z → Path x z
  concat xy yz = Square.missingSide point yz xy

module _ where
  private variable X : Interval → Type{ℓ}
  private variable Y : (i : Interval) → X(i) → Type{ℓ}

  mapPᵢ : (f : (i : Interval) → (x : X i) → Y i x) → ∀{x y} → (path : PathP(\i → X(i)) x y) → PathP(\i → Y i (path(i))) (f Interval.𝟎 x) (f Interval.𝟏 y)
  mapPᵢ(f) p(i) = f i (p(i))
  {-# INLINE mapPᵢ #-}

module _ where
  private variable X : Type{ℓ}
  private variable Y : X → Type{ℓ}
  private variable Z : (x : X) → Y(x) → Type{ℓ}

  -- Maps a path into another space.
  mapP : (f : (x : X) → Y(x)) → ∀{x y} → (path : Path x y) → PathP(\i → Y(path(i))) (f(x)) (f(y))
  mapP(f) p(i) = mapPᵢ(\_ → f) p(i)
  {-# INLINE mapP #-}

  mapP₂ : (f : (x : X) → (y : Y(x)) → Z(x)(y)) → ∀{a₁ b₁ : X}{a₂ : Y(a₁)}{b₂ : Y(b₁)} → (path₁ : Path a₁ b₁) → (path₂ : PathP(\i → Y(path₁ i)) a₂ b₂) → PathP(\i → Z(path₁ i) (path₂ i)) (f a₁ a₂) (f b₁ b₂)
  mapP₂(f) ab1 ab2 i = mapPᵢ (mapP f ab1 $ₚₐₜₕ_) ab2 i
  {-# INLINE mapP₂ #-}

  -- When there is a path between two space mappings.
  mapping : ∀{f g : (x : X) → Y(x)} → (∀{x} → Path(f(x)) (g(x))) → Path f g
  mapping ppt i x = ppt{x} i

  mappingPoint : ∀{f g : (x : X) → Y(x)} → Path f g → (∀{x} → Path(f(x)) (g(x)))
  mappingPoint pfg {x} i = pfg i x

module _ where
  private variable X X₁ X₂ Y Y₁ Y₂ : Type{ℓ}

  map : (f : X → Y) → ∀{a b} → Path a b → Path (f(a)) (f(b))
  map = mapP

  map₂ : (f : X₁ → X₂ → Y) → ∀{a₁ b₁}{a₂ b₂} → Path a₁ b₁ → Path a₂ b₂ → Path (f a₁ a₂) (f b₁ b₂)
  map₂ f ab1 ab2 i = mapP (mapP f ab1 i) ab2 i

  liftedSpaceMap : (S : X → Type{ℓ}) → ∀{a b} → Path a b → S(a) → S(b)
  liftedSpaceMap S p = spaceMap(map S p)

  liftedSpaceMap₂ : (S : X → Y → Type{ℓ}) → ∀{a₁ b₁}{a₂ b₂} → Path a₁ b₁ → Path a₂ b₂ → S a₁ a₂ → S b₁ b₂
  liftedSpaceMap₂ S p q = spaceMap(map₂ S p q)

  liftedSpaceBimap : (S : X → Type{ℓ}) → ∀{a b} → Path a b → S(a) ↔ S(b)
  liftedSpaceBimap S p = spaceBimap(map S p)

  liftedSpaceBimap₂ : (S : X → Y → Type{ℓ}) → ∀{a₁ b₁}{a₂ b₂} → Path a₁ b₁ → Path a₂ b₂ → S a₁ a₂ ↔ S b₁ b₂
  liftedSpaceBimap₂ S p q = spaceBimap(map₂ S p q)

pathPathP : (P : Interval → Type{ℓ}) → ∀{x : P(Interval.𝟎)}{y : P(Interval.𝟏)} → Path(spaceMap(\i → P(i)) x) y ↔ PathP P x y
pathPathP P{x} = intro
  (\p i → Interval.transp(\j → P(Interval.max i j)) i (p i))
  (\p i → Interval.hComp
    (\j → \{
      (i = Interval.𝟎) → x ;
      (i = Interval.𝟏) → p j
    })
    (Interval.transp (\j → P(Interval.min i j)) (Interval.flip i) x)
  )
