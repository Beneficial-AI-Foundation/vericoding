import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
namespace VCHelpers

@[simp] theorem toList_length {α : Type _} {n : Nat} (v : Vector α n) :
  v.toList.length = n := by
  simpa using v.toList_length

end VCHelpers
-- </vc-helpers>

-- <vc-definitions>
def «where» {n : Nat} (condition : Vector Bool n) (x : Vector Int n) (y : Vector Int n) : Vector Int n :=
Vector.ofFn (fun i => if condition[i] then x[i] else y[i])

def whereWithTransform {n : Nat} (arr : Vector Int n) (condition : Int → Bool) (change : Int → Int) : Vector Int n :=
Vector.ofFn (fun i => if condition (arr[i]) then change (arr[i]) else arr[i])
-- </vc-definitions>

-- <vc-theorems>
theorem where_spec {n : Nat} (condition : Vector Bool n) (x : Vector Int n) (y : Vector Int n) :
  («where» condition x y).toList.length = n ∧
  ∀ i : Fin n, («where» condition x y)[i] = (if condition[i] then x[i] else y[i]) ∧
  ∀ arr : Vector Int n, ∀ condition : Int → Bool, ∀ change : Int → Int,
    (whereWithTransform arr condition change).toList.length = n ∧
    ∀ i : Fin n, (whereWithTransform arr condition change)[i] =
      if condition (arr[i]) then change (arr[i]) else arr[i] :=
by
  constructor
  · simpa using VCHelpers.toList_length («where» condition x y)
  · intro i
    constructor
    · simp [«where»]
    · intro arr condition change
      constructor
      · simpa using VCHelpers.toList_length (whereWithTransform arr condition change)
      · intro j
        simp [whereWithTransform]
-- </vc-theorems>
