
module _
  {ℓₒ₁ ℓₘ₁ ℓₒ₂ ℓₘ₂ : Lvl.Level}
  {Obj₁ : Set(ℓₒ₁)}
  {Obj₂ : Set(ℓₒ₂)}
  {_⟶₁_ : Obj₁ → Obj₁ → Set(ℓₘ₁)}
  {_⟶₂_ : Obj₂ → Obj₂ → Set(ℓₘ₂)}
  {Category₁ : Category {_}{_} {Obj₁} _⟶₁_ ⦃ \{x}{y} → Relator.Equals.Proofs.[≡]-equiv {_}{_} {x ⟶₁ y} ⦄ }
  {Category₂ : Category {_}{_} {Obj₂} _⟶₂_ ⦃ \{x}{y} → Relator.Equals.Proofs.[≡]-equiv {_}{_} {x ⟶₂ y} ⦄ }
  where

  open module CategoryWithEquals {ℓₒ}{ℓₘ} {Obj} {_⟶_} = Category {ℓₒ}{ℓₘ} {Obj} {_⟶_} ⦃ \{x}{y} → Relator.Equals.Proofs.[≡]-equiv {_}{_} {x ⟶ y} ⦄
  open Functor

  private
    _∘₁_ = _∘_ (Category₁)
    _∘₂_ = _∘_ (Category₂)

    id₁ = id (Category₁)
    id₂ = id (Category₂)

  module _ where
    open Relator.Equals{ℓₘ₂}
    open Relator.Equals.Proofs{ℓₘ₂}

    record NaturalTransformation
        (F₁ : Functor Category₁ Category₂)
        (F₂ : Functor Category₁ Category₂)
      : Set((ℓₒ₁ Lvl.⊔ ℓₘ₁) Lvl.⊔ (ℓₒ₂ Lvl.⊔ ℓₘ₂))
      where

      private
        functor₁ = functor (F₁)
        functor₂ = functor (F₂)

        map₁ = map (F₁)
        map₂ = map (F₂)

      field
        component : (x : Obj₁) → (functor₁(x) ⟶₂ functor₂(x))

      field
        ⦃ .proof ⦄ : ∀{x y : Obj₁}{f : x ⟶₁ y} → (component(y) ∘₂ map₁(f) ≡ map₂(f) ∘₂ component(x))
    open NaturalTransformation

    {-
    record Monad (T : EndoFunctor Category₁) : Set(ℓₒ₁ Lvl.⊔ ℓₘ₁) where
      private
        _⟹_ = NaturalTransformation
        idNT = identityNaturalTransformation
        _∘NT_ = compositionNaturalTransformation
        _∘F_ = compositionFunctor
        idF = identityFunctor

      field
        -- The ability to construct an endofunctored object from an object.
        -- In Haskell, this is called "return"/"unit" and named "return".
        --   idF ⟹ T
        --   ∀(x: Obj). idF(x) ⟶ T(x)
        --   ∀(x: Obj). x ⟶ T(x)
        η : idF ⟹ T

        -- In Haskell, this is called "join".
        --   (T ∘F T) ⟹ T
        --   ∀(x: Obj). (T ∘F T)(x) ⟶ T(x)
        --   ∀(x: Obj). T(T(x)) ⟶ T(x)
        -- Note: μ = x >>= id (TODO: In some way, this is true?)
        μ : (T ∘F T) ⟹ T

      -- In Haskell, this is called "bind"/"extend" and named "(>>=)". TODO: Not sure. This looks different?
      -- (a → T(b)) → T(a) → T(b)

      -- x >>= f = join (fmap f x)

      -- join x = x >>= id
      -- fmap f x = x >>= (return . f)

      field
        ⦃ .μ-commutativity ⦄ : μ ∘NT (T ∘F μ) ≡ μ ∘NT (μ ∘F T)

        -- μ ∘NT (η ⋅₁ T) ≡ idNT
        -- ∀(x: Obj). (μ ∘NT (η ⋅₁ T))(x) ≡ idNT(x)
        -- ∀(x: Obj). (μ ∘NT (η ⋅₁ T))(x) ≡ idM
        -- ∀(x: Obj). μ(x) ∘M (η ⋅₁ T)(x) ≡ idM
        -- ∀(x: Obj). μ(x) ∘M η(T(x)) ≡ idM
        ⦃ .μ-inverseₗ ⦄ : μ ∘NT (η ⋅₁ T) ≡ idNT

        -- μ ∘NT (T ⋅₂ η) ≡ idNT
        -- ∀(x: Obj). (μ ∘NT (T ⋅₂ η))(x) ≡ idNT(x)
        -- ∀(x: Obj). (μ ∘NT (T ⋅₂ η))(x) ≡ idM
        -- ∀(x: Obj). μ(x) ∘M (T ⋅₂ η)(x) ≡ idM
        -- ∀(x: Obj). μ(x) ∘M map(T) (η(x)) ≡ idM
        ⦃ .μ-inverseᵣ ⦄ : μ ∘NT (T ⋅₂ η) ≡ idNT
    -}

    identityNaturalTransformation : ∀{F : Functor Category₁ Category₂} → NaturalTransformation(F)(F)
    component (identityNaturalTransformation{F}) (_) = id₂
    proof     (identityNaturalTransformation{F}) {x}{y}{f} rewrite identityₗ (Category₂) {functor(F)(x)}{functor(F)(y)}{map(F)(f)}
                                                            | identityᵣ (Category₂) {functor(F)(x)}{functor(F)(y)}{map(F)(f)}
                                                            = [≡]-intro
      -- (component(y) ∘₂ map(f) ≡ map(f) ∘₂ component(x))
      --   component : (x : Obj₁) → (F(x) ⟶₂ F(x))
      --   component(x) = id
      -- ((id: F(y) ⟶₂ F(y)) ∘₂ map(f) ≡ map(f) ∘₂ (id: F(x) ⟶₂ F(x)))
      --   map(f) : F(x) ⟶₂ F(y)
      -- map(f) ≡ map(f)

    module _ {F G H : Functor Category₁ Category₂} (N₁ : NaturalTransformation(G)(H)) (N₂ : NaturalTransformation(F)(G)) where
      private
        η₁ = component(N₁)
        η₂ = component(N₂)

      compositionNaturalTransformation : NaturalTransformation(F)(H)
      component (compositionNaturalTransformation) (x) = η₁(x) ∘₂ η₂(x)
      proof     (compositionNaturalTransformation) {x}{y}{f} rewrite associativity (Category₂) {_}{_}{_}{_} {η₁(y)}     {η₂(y)}     {map(F)(f)}
                                                                    | proof(N₂) {x}{y}{f}
        = symmetry(associativity (Category₂) {_}{_}{_}{_} {η₁(y)}     {map(G)(f)} {η₂(x)})
          🝖 [≡]-with(_∘₂ η₂(x)) (proof(N₁) {x}{y}{f})
          🝖 associativity (Category₂) {_}{_}{_}{_} {map(H)(f)} {η₁(x)}     {η₂(x)}
        -- For x: Obj₁ , y: Obj₁ , f: x ⟶₁ y
        -- Assumptions:
        -- • η₁(y) ∘₂ mapG(f) ≡ mapH(f) ∘₂ η₁(x) //[1]:
        -- • η₂(y) ∘₂ mapF(f) ≡ mapG(f) ∘₂ η₂(x) //[2]:
        -- Conclusion:
        -- • (η₁(y) ∘₂ η₂(y)) ∘₂ mapF(f) ≡ mapH(f) ∘₂ (η₁(x) ∘₂ η₂(x))
        --   η₁(y) ∘₂ mapG(f) ≡ mapH(f) ∘₂ η₁(x) //[1]
        --   (η₁(y) ∘₂ mapG(f)) ∘₂ η₂(x) ≡ (mapH(f) ∘₂ η₁(x)) ∘₂ η₂(x)
        --   η₁(y) ∘₂ (mapG(f) ∘₂ η₂(x)) ≡ (mapH(f) ∘₂ η₁(x)) ∘₂ η₂(x)
        --   η₁(y) ∘₂ (η₂(y) ∘₂ mapF(f)) ≡ (mapH(f) ∘₂ η₁(x)) ∘₂ η₂(x) //[2]
        --   (η₁(y) ∘₂ η₂(y)) ∘₂ mapF(f) ≡ (mapH(f) ∘₂ η₁(x)) ∘₂ η₂(x)
        --   (η₁(y) ∘₂ η₂(y)) ∘₂ mapF(f) ≡ mapH(f) ∘₂ (η₁(x) ∘₂ η₂(x))

  {-
  module _ where
    open Relator.Equals

    open NaturalTransformation

    functorCategory : Category{_}{_} {Functor Category₁ Category₂} (NaturalTransformation)
    _∘_           (functorCategory) = compositionNaturalTransformation
    id            (functorCategory) = identityNaturalTransformation
    identityₗ     (functorCategory) {F}{G} {N} rewrite identityₗ (Category₂) {_}{_} {id₂} = [≡]-intro
      -- For x: Functor(Category₁) (Category₂) , y: Functor(Category₁) (Category₂) , f: NaturalTransformation(x)(y)
      --
      -- identityNaturalTransformation ∘ f
      -- ≡ x ↦ component(identityNaturalTransformation)(x) ∘₂ component(f)(x)
      -- ≡ x ↦ id₂ ∘₂ component(f)(x)
      -- ≡ x ↦ component(f)(x)
      -- ≡ f
    identityᵣ     (functorCategory) = [≡]-intro
    associativity (functorCategory) = [≡]-intro
  -}
