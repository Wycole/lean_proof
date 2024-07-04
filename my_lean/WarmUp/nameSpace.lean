import Mathlib.Tactic
import Mathlib.Analysis.Analytic.Basic

namespace MyRing
variable {R: Type*} [Ring R]


end MyRing


section
variable {G : Type*} [Group G]

namespace Group

theorem mul_right_inv (a : G) : a * a⁻¹ = 1 := by
  have h : (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) = 1 := by
  -- we're proving mul_right_inv, so try to not use it
    rw[mul_assoc, ← mul_assoc a⁻¹ a, mul_left_inv, one_mul, mul_left_inv]
  rw[← h, ← mul_assoc, mul_left_inv, one_mul]

end Group
