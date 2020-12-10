-- TODO: Move some of the proofs from Function.Iteration.Proofs to here so that (_^_) on functions, natural numbers and integers can be generalised.

-- TODO: Maybe something like this
record Iteration(f)(id)(repeat : I → Y) where
  field
    𝟎 : I
    repeat-𝟎 : repeat 𝟎 ≡ id

  record Successor(𝐒 : I → I) where
    field proof : repeat(𝐒(i)) ≡ f(repeat(i))

  record Predecessor(𝐏 : I → I) where
    field proof : f(repeat(𝐏(i))) ≡ repeat(i)
