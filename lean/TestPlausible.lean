import Plausible

namespace TestPlausible

open Plausible

example : ∀ n : Nat, n + 0 = n := by
  plausible
  simp

example : ∀ (xs ys : List Nat), xs ++ ys = ys ++ xs := by
  plausible

#eval Testable.check (∀ n : Nat, n < n + 1)

end TestPlausible