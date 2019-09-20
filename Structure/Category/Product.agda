module Product
  {ℓₒ ℓₘ : Lvl.Level}
  {Obj₁ : Set(ℓₒ)}
  {Obj₂ : Set(ℓₒ)}
  {_⟶₁_ : Obj₁ → Obj₁ → Set(ℓₘ)}
  {_⟶₂_ : Obj₂ → Obj₂ → Set(ℓₘ)}
  where

  open Category
  open Data.Tuple.Proofs
  open Relator.Equals

  [⨯]-obj : Set(ℓₒ)
  [⨯]-obj = Tuple._⨯_ Obj₁ Obj₂

  [⨯]-morphism : [⨯]-obj → [⨯]-obj → Set(ℓₘ)
  [⨯]-morphism(x₁ , x₂) (y₁ , y₂) = Tuple._⨯_ (x₁ ⟶₁ y₁) (x₂ ⟶₂ y₂)

  _⨯_ : Category(_⟶₁_) → Category(_⟶₂_) → Category{_}{_} {[⨯]-obj} [⨯]-morphism
  _∘_ (_⨯_ cat₁ cat₂) {x₁ , x₂}{y₁ , y₂}{z₁ , z₂} (yz₁ , yz₂) (xy₁ , xy₂) = (_∘_ cat₁ yz₁ xy₁ , _∘_ cat₂ yz₂ xy₂)
  id  (_⨯_ cat₁ cat₂) {x₁ , x₂} = (id cat₁ {x₁} , id cat₂ {x₂})
  identityₗ (_⨯_ cat₁ cat₂) {x₁ , x₂}{y₁ , y₂} {f₁ , f₂} = Tuple-equality (identityₗ cat₁ {x₁}{y₁} {f₁}) (identityₗ cat₂ {x₂}{y₂} {f₂})
  identityᵣ (_⨯_ cat₁ cat₂) {x₁ , x₂}{y₁ , y₂} {f₁ , f₂} = Tuple-equality (identityᵣ cat₁ {x₁}{y₁} {f₁}) (identityᵣ cat₂ {x₂}{y₂} {f₂})
  associativity (_⨯_ cat₁ cat₂) {x₁ , x₂}{y₁ , y₂}{z₁ , z₂}{w₁ , w₂} {f₁ , f₂}{g₁ , g₂}{h₁ , h₂} = Tuple-equality (associativity cat₁ {x₁}{y₁}{z₁}{w₁} {f₁}{g₁}{h₁}) (associativity cat₂ {x₂}{y₂}{z₂}{w₂} {f₂}{g₂}{h₂})
