module Sets.Setoid where -- TODO: Should probably rename. Not really like a traditional setoid

record SetEq (T : Set) : Set₁ where
  constructor setEq
  field
    _≡_ : T → T → Set

  field
    ⦃ [≡]-reflexivity ⦄  : ∀{x : T}     → (x ≡ x)
    ⦃ [≡]-symmetry ⦄     : ∀{x y : T}   → (x ≡ y) → (y ≡ x)
    ⦃ [≡]-transitivity ⦄ : ∀{x y z : T} → (x ≡ y) → (y ≡ z) → (x ≡ z)
open SetEq ⦃ ... ⦄ public

record Congruence (T₁ : Set) (T₂ : Set) (_≡₁_ : T₁ → T₁ → Set) (_≡₂_ : T₂ → T₂ → Set) : Set where
  field
    congruence : (f : T₁ → T₂) → ∀{x y : T₁} → (x ≡₁ y) → (f(x) ≡₂ f(y))

record Setoid : Set₁ where
  field
    Type : Set
    instance ⦃ Eq ⦄ : SetEq(Type)

  field
    [≡]-with : ∀{Type₂} → ⦃ _ : SetEq(Type₂) ⦄ → Congruence(Type)(Type₂) (_≡_) (_≡_) -- TODO: Is this possible?

[≡]-with : ∀{S₁ S₂ : Setoid} → (f : Setoid.Type(S₁) → Setoid.Type(S₂)) → ∀{x y} → (x ≡ y) → (f(x) ≡ f(y))
[≡]-with{S₁}{S₂} = Congruence.congruence(Setoid.[≡]-with (S₁) {Setoid.Type(S₂)})

-- setoid : (T : Set) → (T → T → Set) → Setoid
-- setoid(T)(_≡_) = record{ Type = T ; Eq = setEq(_≡_) }
