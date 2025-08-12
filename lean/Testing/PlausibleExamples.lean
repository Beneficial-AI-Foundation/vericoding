import Plausible
import Mathlib.Data.List.Basic
import Testing.PlausibleUtils

namespace Testing.PlausibleExamples

open Plausible Testing.PlausibleUtils

section ListProperties

example : ∀ (xs ys : List Nat), xs ++ ys = ys ++ xs := by
  plausible

example : ∀ (xs : List Nat), xs.reverse.reverse = xs := by
  plausible

example : ∀ (xs : List Nat) (x : Nat), (x :: xs).length = xs.length + 1 := by
  plausible

end ListProperties

section FunctionProperties

def isEven (n : Nat) : Bool := n % 2 = 0

example : ∀ n : Nat, isEven n → isEven (n + 2) := by
  plausible

example : ∀ n : Nat, isEven n ↔ ¬isEven (n + 1) := by
  plausible

end FunctionProperties

end Testing.PlausibleExamples