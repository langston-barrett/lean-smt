import Smt

set_option linter.unusedVariables false

-- Under `trust`, normalization and embedding skip the proofs of `∀` and `→`. The
-- goal must still be simplified as without `trust`: `Nat`s embedded into `Int`s,
-- and `Bool`s into `Prop`s, under binders and in hypotheses.

example (x y z : Nat) (b : Bool) (h₁ : x < y) (h₂ : y < z) (h₃ : b = true → x = 0) (h₄ : ∀ n : Nat, n + x ≥ x) :
    x < z := by
  smt +trust [h₁, h₂, h₃, h₄]

example (f : Nat → Nat) (h : ∀ n m : Nat, n ≤ m → f n ≤ f m) (a b : Nat) (hab : a ≤ b) : f a ≤ f b := by
  smt +trust [h, hab]

-- `sat` is still reported.
example (x y : Nat) (h : x ≤ y) : x < y := by
  smt +trust [h]
