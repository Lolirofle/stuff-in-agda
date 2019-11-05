
  module NumeralNaturalProofs where
    open NumeralNatural
    open Structure
    open Structure.Function'.Properties
    open Structure.Relator
    open Structure.Relator.Properties

    [∩]-inductive : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ (Inductive(a) ∧ Inductive(b)) ⟶ Inductive(a ∩ b))))
    [∩]-inductive =
      ([∀].intro (\{a} →
        ([∀].intro (\{b} →
          ([→].intro(indaindb ↦
            ([∧].intro
              -- ∅ is in
              ([↔].elimₗ
                ([∀].elim([∀].elim([∀].elim([∩]-inclusion){a}){b}){∅})
                ([∧].intro
                  ([∧].elimₗ([∧].elimₗ indaindb))
                  ([∧].elimₗ([∧].elimᵣ indaindb))
                )
              )

              -- 𝐒 is in
              ([∀].intro (\{x} →
                ([→].intro(x∈a∩b ↦
                  ([↔].elimₗ
                    ([∀].elim([∀].elim([∀].elim([∩]-inclusion){a}){b}){𝐒(x)})
                    ([∧].intro
                      -- 𝐒(x) ∈ a
                      ([→].elim([∀].elim([∧].elimᵣ([∧].elimₗ indaindb)){x})(
                        -- x ∈ a
                        [∧].elimₗ([↔].elimᵣ
                          ([∀].elim([∀].elim([∀].elim([∩]-inclusion){a}){b}){x})
                          (x∈a∩b)
                        )
                      ))

                      -- 𝐒(x) ∈ b
                      ([→].elim([∀].elim([∧].elimᵣ([∧].elimᵣ indaindb)){x})(
                        -- x ∈ b
                        [∧].elimᵣ([↔].elimᵣ
                          ([∀].elim([∀].elim([∀].elim([∩]-inclusion){a}){b}){x})
                          (x∈a∩b)
                        )
                      ))
                    )
                  )
                ))
              ))
            )
          ))
        ))
      ))

    -- postulate [⋂]-property : ∀{φ} → Proof(∀ₗ(s ↦ ∀ₗ(x ↦ (x ∈ s) ⟶ φ(x)) ⟶ φ(⋂ s))) TODO: MAybe not true
    [⋂]-inductive : Proof(∀ₗ(s ↦ ∀ₗ(x ↦ (x ∈ s) ⟶ Inductive(x)) ⟶ Inductive(⋂ s)))
    [⋂]-inductive =
      ([∀].intro (\{s} →
        ([→].intro(allxxsindx ↦
          ([∧].intro
            -- ∅ is in
            proof

            -- 𝐒 is in
            proof
          )
        ))
      ))
      where postulate proof : ∀{a} → a

    [ℕ]-inductive : Proof(Inductive(ℕ))
    [ℕ]-inductive =
      ([→].elim
        ([∀].elim
          [⋂]-inductive
          {filter(℘(inductiveSet)) Inductive}
        )
        ([∀].intro(\{x} →
          ([→].intro(x∈filter ↦
            [∧].elimᵣ(([↔].elimᵣ([∀].elim([∀].elim filter-inclusion{℘(inductiveSet)}){x})) (x∈filter))
          ))
        ))
      )

    module _ where
      open FunctionSet
      open FunctionProofs

      postulate [ℕ]-recursive-function : ∀{z : Domain}{s : Domain → Domain → Domain} → Proof(∃ₛ!(ℕ →ₛₑₜ ℕ)(f ↦ ((𝟎 , z) ∈ f) ∧ (∀ₗ(n ↦ ∀ₗ(fn ↦ ((n , fn) ∈ f) ⟶ ((𝐒(n) , s(n)(fn)) ∈ f))))))

      [ℕ]-recursive-function-witness : Domain → BinaryOperator → Function
      [ℕ]-recursive-function-witness z s = [→ₛₑₜ]-witness([∃ₛ!]-witness ⦃ f ⦄ ) ⦃ [∃ₛ!]-domain ⦃ f ⦄ ⦄ where
        f = [ℕ]-recursive-function{z}{s}

      postulate [ℕ]-recursive-function-of-zero : ∀{z : Domain}{s : Domain → Domain → Domain} → Proof(([ℕ]-recursive-function-witness z s)(𝟎) ≡ z)
      postulate [ℕ]-recursive-function-of-successor : ∀{z : Domain}{s : Domain → Domain → Domain} → Proof(∀ₛ(ℕ) (n ↦ ([ℕ]-recursive-function-witness z s)(𝐒(n)) ≡ s(n)(([ℕ]-recursive-function-witness z s)(n))))

      _+_ : Domain → Domain → Domain
      _+_ a b = [ℕ]-recursive-function-witness z s b where
        z : Domain
        z = a

        s : Domain → Domain → Domain
        s(n)(sn) = 𝐒(sn)

      _⋅_ : Domain → Domain → Domain
      _⋅_ a b = [ℕ]-recursive-function-witness z s b where
        z : Domain
        z = 𝟎

        s : Domain → Domain → Domain
        s(n)(sn) = sn + a

      _^'_ : Domain → Domain → Domain -- TODO: Temporary name collision fix
      _^'_ a b = [ℕ]-recursive-function-witness z s b where
        z : Domain
        z = 𝐒(𝟎)

        s : Domain → Domain → Domain
        s(n)(sn) = sn ⋅ a

      module _ where
        open Structure.Operator.Properties

        postulate [+]-commutativity : Proof(Commutativity(ℕ)(_+_))
        postulate [+]-associativity : Proof(Associativity(ℕ)(_+_))
        postulate [+]-identity : Proof(Identity(ℕ)(_+_)(𝟎))

        postulate [⋅]-commutativity : Proof(Commutativity(ℕ)(_⋅_))
        postulate [⋅]-associativity : Proof(Associativity(ℕ)(_⋅_))
        postulate [⋅]-identity : Proof(Identity(ℕ)(_⋅_)(𝐒(𝟎)))

        postulate [⋅][+]-distributivity : Proof(Distributivity(ℕ)(_⋅_)(_+_))

    postulate [ℕ]-elements : Proof(∀ₛ(ℕ)(n ↦ (n ≡ 𝟎) ∨ ∃ₛ(ℕ)(p ↦ n ≡ 𝐒(p))))

    postulate [<]-irreflexivity : Proof(Irreflexivity(ℕ)(_<_))
    postulate [<]-asymmetry     : Proof(Antisymmetry(ℕ)(_<_))
    postulate [<]-transitivity  : Proof(Transitivity(ℕ)(_<_))

    postulate [≤]-reflexivity  : Proof(Irreflexivity(ℕ)(_≤_))
    postulate [≤]-antisymmetry : Proof(Antisymmetry(ℕ)(_≤_))
    postulate [≤]-transitivity : Proof(Transitivity(ℕ)(_≤_))



    -- instance
    --   [𝐒]-type : Function.Type(𝐒)
    --   [𝐒]-type = Function.Type.intro ℕ ℕ proof where
    --     postulate proof : ∀{a} → a

    -- postulate [𝐒]-injective : Proof(Injective(ℕ)(𝐒))

    -- ∀ₛ(ℕ)(a ↦ ∀ₛ(ℕ)(b ↦ (a < b) ⟶ (𝐒(a) < 𝐒(b))))
    -- ∀ₛ(ℕ)(n ↦ 𝟎 ≢ 𝐒(n))

  -- A model of the integers expressed in set theory (using only sets).
  module NumeralInteger where
    open Structure.Function'.Properties
    open Structure.Relator.Properties
    private
      module Nat where
        open NumeralNatural ⦃ signature ⦄ public
        open NumeralNaturalProofs public

    EqualDistance : Domain → Domain → Formula
    EqualDistance x y = ∃ₗ(x₁ ↦ ∃ₗ(x₂ ↦ (x ≡ (x₁ , x₂)) ∧ ∃ₗ(y₁ ↦ ∃ₗ(y₂ ↦ (y ≡ (y₁ , y₂)) ∧ ((x₁ Nat.+ y₂) ≡ (x₂ Nat.+ y₁))))))

    postulate EqualDistance-equivalence : Proof(Equivalence(Nat.ℕ ⨯ Nat.ℕ)(EqualDistance))

    ℤ : Domain
    ℤ = (Nat.ℕ ⨯ Nat.ℕ) / EqualDistance

    nat : Domain → Domain
    nat(n) = map(N ↦ (N , (N Nat.+ n))) Nat.ℕ

    postulate nat-type : Proof(Type(Nat.ℕ)(ℤ)(nat))

    𝟎 : Domain
    𝟎 = nat(Nat.𝟎)

    postulate _<_ : Domain → Domain → Formula -- TODO

    _≤_ : Domain → Domain → Formula
    a ≤ b = (a < b) ∨ (a ≡ b)

    _>_ : Domain → Domain → Formula
    _>_ = swap _<_

    _≥_ : Domain → Domain → Formula
    _≥_ = swap _≤_

    ℕ : Domain
    ℕ = filter(ℤ) (_≥ 𝟎)

    ℤ₊ : Domain
    ℤ₊ = filter(ℤ) (_> 𝟎)

    ℤ₋ : Domain
    ℤ₋ = filter(ℤ) (_< 𝟎)

    postulate 𝐒 : Domain → Domain -- TODO

    postulate 𝐏 : Domain → Domain -- TODO

    postulate _+_ : Domain → Domain → Domain -- TODO

    postulate −_ : Domain → Domain -- TODO

    _−_ : Domain → Domain → Domain
    a − b = a + (− b)

    postulate _⋅_ : Domain → Domain → Domain -- TODO

  -- A model of the rational numbers expressed in set theory (using only sets).
  module NumeralRational where
    open Structure.Function'.Properties
    open Structure.Relator.Properties
    private module Nat = NumeralNatural
    private module Int = NumeralInteger
    open Structure.Ordering.Strict

    EqualRatio : Domain → Domain → Formula
    EqualRatio x y = ∃ₗ(x₁ ↦ ∃ₗ(x₂ ↦ (x ≡ (x₁ , x₂)) ∧ ∃ₗ(y₁ ↦ ∃ₗ(y₂ ↦ (y ≡ (y₁ , y₂)) ∧ ((x₁ Int.⋅ y₂) ≡ (x₂ Int.⋅ y₁))))))

    postulate EqualRatio-equivalence : Proof(Equivalence(Int.ℤ ⨯ Int.ℤ₊)(EqualRatio))

    ℚ : Domain
    ℚ = (Int.ℤ ⨯ Int.ℤ₊) / EqualRatio

    postulate int : Domain → Domain -- TODO
    -- int(n) = map(N ↦ (N , (N Int.⋅ n))) Int.ℤ

    postulate int-type : Proof(Type(Int.ℤ)(ℚ)(int))

    nat : Domain → Domain
    nat(n) = int(Int.nat(n))

    postulate nat-type : Proof(Type(Nat.ℕ)(ℚ)(nat))

    𝟎 : Domain
    𝟎 = nat(Nat.𝟎)

    -- TODO: These are incorrect because elements in ℚ are sets of tuples
    _≤_ : Domain → Domain → Formula
    _≤_ x y = ∃ₗ(x₁ ↦ ∃ₗ(x₂ ↦ (x ≡ (x₁ , x₂)) ∧ ∃ₗ(y₁ ↦ ∃ₗ(y₂ ↦ (y ≡ (y₁ , y₂)) ∧ ((x₁ Int.⋅ y₂) Int.≤ (x₂ Int.⋅ y₁))))))

    _<_ : Domain → Domain → Formula
    _<_ x y = ∃ₗ(x₁ ↦ ∃ₗ(x₂ ↦ (x ≡ (x₁ , x₂)) ∧ ∃ₗ(y₁ ↦ ∃ₗ(y₂ ↦ (y ≡ (y₁ , y₂)) ∧ ((x₁ Int.⋅ y₂) Int.< (x₂ Int.⋅ y₁))))))

    _>_ : Domain → Domain → Formula
    _>_ = swap _<_

    _≥_ : Domain → Domain → Formula
    _≥_ = swap _≤_

    postulate [<]-dense : Proof(Dense(ℚ)(_<_)) -- TODO

    postulate _+_ : Domain → Domain → Domain -- TODO

    postulate −_ : Domain → Domain -- TODO

    _−_ : Domain → Domain → Domain
    a − b = a + (− b)

    postulate _⋅_ : Domain → Domain → Domain -- TODO

    postulate ⅟_ : Domain → Domain -- TODO

    _/'_ : Domain → Domain → Domain
    a /' b = a ⋅ (⅟ b)

    postulate abs : Domain → Domain

    _𝄩_ : Domain → Domain → Domain
    a 𝄩 b = abs(a − b)

  -- A model of the real numbers expressed in set theory (using only sets).
  module NumeralReal where
    private module Rat = NumeralRational

-- TODO: https://math.stackexchange.com/questions/1076806/proof-that-the-floor-and-ceiling-functions-exist
