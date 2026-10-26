import Smt

-- Inductive types with type parameters become SMT-LIB parametric datatypes (`par`), and their
-- instances sort applications such as `(Opt Int)`.

inductive Opt (T : Type) where
  | none
  | some (val : T)

inductive Lst (T : Type) where
  | nil
  | cons (hd : T) (tl : Lst T)

structure Pair (A B : Type) where
  fst : A
  snd : B

example (x : Opt Int) (h : x = Opt.some 3) : x ≠ Opt.none := by
  smt [h]

-- Recursive.
example (xs : Lst Int) (h : xs = Lst.cons 1 Lst.nil) : xs ≠ Lst.nil := by
  smt [h]

-- Nested.
example (y : Opt (Lst Int)) (h : y = Opt.some (Lst.cons 1 Lst.nil)) : y ≠ Opt.none := by
  smt [h]

-- Two instances of one datatype.
example (x : Opt Int) (b : Opt (Lst Int)) (h : x = Opt.none) (hb : b = Opt.some Lst.nil) :
    x = Opt.none ∧ b ≠ Opt.none := by
  smt [h, hb]

-- Several parameters. The proof that equal constructors with distinct fields differ is not
-- reconstructed yet, for parametric and other datatypes alike.
example (p : Pair Int (Opt Int)) (h : p = Pair.mk 1 Opt.none) : p ≠ Pair.mk 1 (Opt.some 2) := by
  smt +trust [h]

-- A counterexample with a value of a parametric datatype.
example (x : Opt (Lst Int)) (h : x ≠ Opt.none) : x = Opt.some (Lst.cons 3 Lst.nil) := by
  smt +model [h]
