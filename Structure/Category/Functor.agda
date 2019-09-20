
module _
  {ℓₒ₁ ℓₘ₁ ℓₒ₂ ℓₘ₂ : Lvl.Level}
  {Obj₁ : Set(ℓₒ₁)}
  {Obj₂ : Set(ℓₒ₂)}
  {_⟶₁_ : Obj₁ → Obj₁ → Set(ℓₘ₁)}
  {_⟶₂_ : Obj₂ → Obj₂ → Set(ℓₘ₂)}
  where

  open Relator.Equals
  open Relator.Equals.Proofs

  -- A covariant functor.
  -- A homomorphism between categories.
  -- "Preserves structure"
  record Functor
      (Category₁ : Category {_}{_} {Obj₁} (_⟶₁_) ⦃ \{x}{y} → [≡]-equiv {_}{_} {x ⟶₁ y} ⦄)
      (Category₂ : Category {_}{_} {Obj₂} (_⟶₂_) ⦃ \{x}{y} → [≡]-equiv {_}{_} {x ⟶₂ y} ⦄)
    : Set((ℓₒ₁ Lvl.⊔ ℓₘ₁) Lvl.⊔ (ℓₒ₂ Lvl.⊔ ℓₘ₂))
    where

    private
      _∘₁_ = Category._∘_ (Category₁)
      _∘₂_ = Category._∘_ (Category₂)

      id₁ = Category.id (Category₁)
      id₂ = Category.id (Category₂)

    field
      -- Morphs/Transforms objects from category 1 to category 2
      functor : Obj₁ → Obj₂

      -- Morphs/Transforms morphisms from category 1 to category 2
      map : ∀{x y} → (x ⟶₁ y) → (functor(x) ⟶₂ functor(y))

    field
     ⦃ .[∘]-preserving ⦄ : ∀{x y z}{f : y ⟶₁ z}{g : x ⟶₁ y} → (map(f ∘₁ g) ≡ map(f) ∘₂ map(g))
     ⦃ .id-preserving  ⦄ : ∀{x} → (map(id₁{x}) ≡ id₂)

    .isomorphism-preserving : ∀{x y}{f : x ⟶₁ y} → Category.Isomorphism(Category₁)(f) → Category.Isomorphism(Category₂)(map f)
    isomorphism-preserving {x}{y} {f} ([∃]-intro g ⦃ [∧]-intro gfid fgid ⦄) = [∃]-intro (map g) ⦃ [∧]-intro proofₗ proofᵣ ⦄ where
      .proofₗ : map(g) ∘₂ map(f) ≡ id₂
      proofₗ =
        (symmetry [∘]-preserving :of: (map(g) ∘₂ map(f) ≡ map(g ∘₁ f)))
        🝖 ([≡]-with(map) gfid    :of: (_                ≡ map(id₁)))
        🝖 (id-preserving         :of: (_                ≡ id₂))

      .proofᵣ : map(f) ∘₂ map(g) ≡ id₂
      proofᵣ =
        (symmetry [∘]-preserving :of: (map(f) ∘₂ map(g) ≡ map(f ∘₁ g)))
        🝖 ([≡]-with(map) fgid    :of: (_                ≡ map(id₁)))
        🝖 (id-preserving         :of: (_                ≡ id₂))

  constantFunctor : (obj₂ : Obj₂) → (cat₁ : _) → (cat₂ : _) → Functor(cat₁)(cat₂)
  Functor.functor       (constantFunctor(obj₂) (_)(cat₂)) = const(obj₂)
  Functor.map           (constantFunctor(obj₂) (_)(cat₂)) = const(Category.id(cat₂) {obj₂})
  Functor.[∘]-preserving(constantFunctor(obj₂) (_)(cat₂)) = symmetry (Category.identityₗ(cat₂))
  Functor.id-preserving (constantFunctor(obj₂) (_)(cat₂)) = [≡]-intro

module _ {ℓₒ ℓₘ : Lvl.Level} where -- TODO: Level problems. Probably in the proofs {ℓₒ₁}{ℓₘ₁} {ℓₒ₂}{ℓₘ₂} {ℓₒ₃}{ℓₘ₃}
  private
    ℓₒ₁ = ℓₒ
    ℓₘ₁ = ℓₘ
    ℓₒ₂ = ℓₒ
    ℓₘ₂ = ℓₘ
    ℓₒ₃ = ℓₒ
    ℓₘ₃ = ℓₘ

  open Relator.Equals.Proofs{ℓₘ₂}

  compositionFunctor : ∀{Obj₁}{Obj₂}{Obj₃} {M₁}{M₂}{M₃} {cat₁}{cat₂}{cat₃}
                     → Functor{ℓₒ₂}{ℓₘ₂} {ℓₒ₃}{ℓₘ₃} {Obj₂}{Obj₃}{M₂}{M₃} (cat₂)(cat₃)
                     → Functor{ℓₒ₁}{ℓₘ₁} {ℓₒ₂}{ℓₘ₂} {Obj₁}{Obj₂}{M₁}{M₂} (cat₁)(cat₂)
                     → Functor{ℓₒ₁}{ℓₘ₁} {ℓₒ₃}{ℓₘ₃} {Obj₁}{Obj₃}{M₁}{M₃} (cat₁)(cat₃)
  Functor.functor       (compositionFunctor (functor₂₃)(functor₁₂)) = Functor.functor(functor₂₃) ∘f Functor.functor(functor₁₂)
  Functor.map           (compositionFunctor (functor₂₃)(functor₁₂)){x}{y} = (Functor.map(functor₂₃){Functor.functor(functor₁₂)(x)}{Functor.functor(functor₁₂)(y)}) ∘f (Functor.map(functor₁₂){x}{y})
  Functor.[∘]-preserving(compositionFunctor (functor₂₃)(functor₁₂)) =
    ([≡]-with(Functor.map(functor₂₃))
      (Functor.[∘]-preserving(functor₁₂))
    )
    🝖 (Functor.[∘]-preserving(functor₂₃))
  Functor.id-preserving (compositionFunctor (functor₂₃)(functor₁₂)) =
    ([≡]-with(expr ↦ Functor.map(functor₂₃)(expr))
      (Functor.id-preserving(functor₁₂))
    )
    🝖 (Functor.id-preserving(functor₂₃))
  -- • {
  --     map₁₂(f ∘₁ g) ≡ map₁₂(f) ∘₂ map₁₂(g)
  --     map₂₃(map₁₂(f ∘₁ g)) ≡ map₂₃(map₁₂(f) ∘₂ map₁₂(g))
  -- }
  -- • map₂₃(f ∘₂ g) ≡ map₂₃(f) ∘₃ map₂₃(g)
  -- ⇒ map₂₃(map₁₂(f ∘₁ g)) ≡ map₂₃(map₁₂(f)) ∘₂ map₂₃(map₁₂(g))


module _ {ℓₒ ℓₘ} where
  open Relator.Equals

  -- A covariant functor from a category to itself
  EndoFunctor : ∀{Obj : Set(ℓₒ)} {_⟶_ : Obj → Obj → Set(ℓₘ)} → Category{_}{_} {Obj}(_⟶_) → Set(ℓₒ Lvl.⊔ ℓₘ)
  EndoFunctor {Obj}{_⟶_} (Category) = Functor {ℓₒ}{ℓₘ}{ℓₒ}{ℓₘ} {Obj}{Obj} {_⟶_}{_⟶_} (Category)(Category)

  identityFunctor : ∀{Obj}{_⟶_} → (cat : _) → EndoFunctor{Obj}{_⟶_} (cat)
  Functor.functor       (identityFunctor(_)) = Functional.id
  Functor.map           (identityFunctor(_)) = Functional.id
  Functor.[∘]-preserving(identityFunctor(_)) = [≡]-intro
  Functor.id-preserving (identityFunctor(_)) = [≡]-intro
