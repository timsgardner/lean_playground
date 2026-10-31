import Mathlib.Tactic.Convert

inductive N where
  | z : N
  | s : N → N

namespace N

/-- Addition recursing on the second argument, like core `Nat.add`.
    So `add m z` reduces to `m` by computation, but `add z m` does not. -/
def add : N → N → N
  | m, z   => m
  | m, s n => s (add m n)

/-- Internals don't matter here. Point is that for any `n : N`,
  `add z n` and `n` are propositionally (by this proposition),
  but not definitionally, equal. -/
theorem z_add : ∀ n : N, add z n = n
  | z   => rfl
  | s n => congrArg s (z_add n)   -- induction: `add z (s n)` computes to `s (add z n)`

inductive Even : N → Prop where
  | z : Even z
  | ss {n : N} : Even n → Even (s (s n))

end N
open N

example (n : N) (h : Even (add z n)) : Even n := by
  -- exact h            -- fails: `Even (add z n)` is not defeq to `Even n`
  -- The current goal is `n.Even`.
  -- We have `h : (z.add n).Even`.
  -- We can turn h into our goal of n.Even if we can substitute
  -- `n` for `z.add n` in `(z.add n).Even`, making `n.Even`.
  -- `convert h` sees that we will discharge the current goal by
  -- such a substitution, and therefore that we will discharge the
  -- current goal by proving `n = z.add n` (or `n = add z n`),
  -- which would endorse the substitution.
  convert h
  -- ⊢ n = add z n
  exact (z_add n).symm


-- Here's an even more bare-bones example, with no
-- inductive cleverness.
example
    (T1 T2 : Type*)
    (x y : T1)
    (h: x = y)
    (f: T1 → T2)
    : f x = f y := by
  -- Here `congr` discharges immediately.
  congr
