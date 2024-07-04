import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Util.Delaborators


/-
proof of Lemma - Rules of arithmetic (p.29)
x,y,z,w are elements of field (K, +, *)
-/
namespace MyField
variable {K : Type*}[Field K]
variable {x y z : K}

-- 1. x + y = x + z → y = z
theorem add_left_cancel (h : x + y = x + z) : y = z := by
  rw[← neg_add_cancel_left x y, h, neg_add_cancel_left]

-- 2. -(-x) = x and - x = (-1) * x
theorem neg_neg : - -x = x := by
  -- have h : x - x = 0 := by rw[sub_self]
  -- rw[← add_neg_cancel_left (- x) (-(-x))]
  -- rw[← sub_eq_add_neg, add_sub, ← sub_eq_add_neg, sub_self]
  sorry

theorem neg_eq_neg_one_mul : -x = (-1) * x := by
  have h: (-1) * x = - (1 * x) := by
    rw[one_mul,]
    --have h': - x = (-1) * x := by
  sorry

-- 3. x * (−y) = −(x * y)
theorem mul_neg_eq_neg_mul : x * (- y) = - (x * y) := by
  sorry

-- 4. x * y = x * z, x ≠ 0 → y = z

-- 5. x * y = 0  → x = 0 or y = 0


end MyField
