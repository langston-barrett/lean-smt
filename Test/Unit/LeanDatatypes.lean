import Smt

-- Lean's own universe-polymorphic inductive types, `Option` and `Except`, become parametric
-- datatypes, at universe 0, and their values are read back from a model.

set_option trace.smt true in
example (x : Option Int) (e : Except Bool Int) (h : x = Option.some 3) (he : e = Except.ok 2) :
    x ≠ Option.none ∧ e ≠ Except.error true := by
  smt +trust [h, he]

-- Nested.
example (x : Option (Option Bool)) (h : x = .some .none) : x ≠ .none := by
  smt +trust [h]

-- Counterexamples with values of both.
example (x : Option Int) (h : x ≠ Option.none) : x = Option.some 3 := by
  smt +model [h]

example (e : Except Bool Int) (h : e ≠ Except.ok 2) : e = Except.error true := by
  smt +model [h]
