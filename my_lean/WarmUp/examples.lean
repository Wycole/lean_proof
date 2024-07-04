import Mathlib.Tactic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Algebra.Ring.Defs

section

variable (a b c : ℝ)  -- property will hold for this section

example (a b c : ℝ ) : a + b + c = a + (b + c) := by
  rw[add_assoc a b c]

-- we can omit the type of a b c here, as we already wrote it in line 7
example : a + (b + c) = a + b + c := by
  rw[← add_assoc a b c]

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  rw[mul_add (a + b) c d, add_mul a b c, add_mul a b d]
  rw[← add_assoc, add_assoc (a * c) _ _, add_comm (b * c) (a * d), ← add_assoc]
-- or
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  rw[add_mul a b (a - b)]
  ring

example (h: a * b = c) : (a * b) * c = c ^ 2 := by
  rw[h, pow_two]

end
