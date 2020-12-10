
module _ {T : Type{ℓₒ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  instance
    PredSet-setLike : SetLike{C = PredSet{ℓ}(T) ⦃ equiv ⦄} (_∈_)
    SetLike._⊆_ PredSet-setLike = _⊆_
    SetLike._≡_ PredSet-setLike = _≡_
    SetLike.[⊆]-membership PredSet-setLike = [↔]-intro intro _⊆_.proof
    SetLike.[≡]-membership PredSet-setLike = [↔]-intro intro _≡_.proof

  instance
    PredSet-emptySet : SetLike.EmptySet{C = PredSet{ℓ}(T) ⦃ equiv ⦄} (_∈_)
    SetLike.EmptySet.∅          PredSet-emptySet = ∅
    SetLike.EmptySet.membership PredSet-emptySet ()

  instance
    PredSet-universalSet : SetLike.UniversalSet{C = PredSet{ℓ}(T) ⦃ equiv ⦄} (_∈_)
    SetLike.UniversalSet.𝐔          PredSet-universalSet = 𝐔
    SetLike.UniversalSet.membership PredSet-universalSet = record {}

  instance
    PredSet-unionOperator : SetLike.UnionOperator{C = PredSet{ℓ}(T) ⦃ equiv ⦄} (_∈_)
    SetLike.UnionOperator._∪_        PredSet-unionOperator = _∪_
    SetLike.UnionOperator.membership PredSet-unionOperator = [↔]-intro id id

  instance
    PredSet-intersectionOperator : SetLike.IntersectionOperator{C = PredSet{ℓ}(T) ⦃ equiv ⦄} (_∈_)
    SetLike.IntersectionOperator._∩_        PredSet-intersectionOperator = _∩_
    SetLike.IntersectionOperator.membership PredSet-intersectionOperator = [↔]-intro id id

  instance
    PredSet-complementOperator : SetLike.ComplementOperator{C = PredSet{ℓ}(T) ⦃ equiv ⦄} (_∈_)
    SetLike.ComplementOperator.∁          PredSet-complementOperator = ∁_
    SetLike.ComplementOperator.membership PredSet-complementOperator = [↔]-intro id id

module _ {T : Type{ℓ}} ⦃ equiv : Equiv{ℓ}(T) ⦄ where -- TODO: Levels in SetLike
  instance
    PredSet-mapFunction : SetLike.MapFunction{C₁ = PredSet{ℓ}(T) ⦃ equiv ⦄}{C₂ = PredSet{ℓ}(T) ⦃ equiv ⦄} (_∈_)(_∈_)
    SetLike.MapFunction.map        PredSet-mapFunction f = map f
    SetLike.MapFunction.membership PredSet-mapFunction   = [↔]-intro id id

  instance
    PredSet-unmapFunction : SetLike.UnmapFunction{C₁ = PredSet{ℓ}(T) ⦃ equiv ⦄}{C₂ = PredSet{ℓ}(T) ⦃ equiv ⦄} (_∈_)(_∈_)
    SetLike.UnmapFunction.unmap      PredSet-unmapFunction = unmap
    SetLike.UnmapFunction.membership PredSet-unmapFunction = [↔]-intro id id

  instance
    PredSet-unapplyFunction : SetLike.UnapplyFunction{C = PredSet{ℓ}(T) ⦃ equiv ⦄} (_∈_) {O = T}
    SetLike.UnapplyFunction.unapply    PredSet-unapplyFunction = unapply
    SetLike.UnapplyFunction.membership PredSet-unapplyFunction = [↔]-intro id id

  instance
    PredSet-filterFunction : SetLike.FilterFunction{C = PredSet{ℓ}(T) ⦃ equiv ⦄} (_∈_) {ℓ}{ℓ}
    SetLike.FilterFunction.filter     PredSet-filterFunction = filter
    SetLike.FilterFunction.membership PredSet-filterFunction = [↔]-intro id id

{- TODO: SetLike is not general enough
module _ {T : Type{ℓ}} ⦃ equiv : Equiv{ℓ}(T) ⦄ where
  instance
    -- PredSet-bigUnionOperator : SetLike.BigUnionOperator{Cₒ = PredSet(PredSet(T) ⦃ {!!} ⦄) ⦃ {!!} ⦄} {Cᵢ = PredSet(T) ⦃ {!!} ⦄} (_∈_)(_∈_)
    SetLike.BigUnionOperator.⋃          PredSet-bigUnionOperator = {!⋃!}
    SetLike.BigUnionOperator.membership PredSet-bigUnionOperator = {!!}
-}
