import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def list_mean (l : List Float) : Float :=
  match l with
  | [] => 0.0
  | _ => (List.sum l) / Float.ofNat l.length

-- LLM HELPER
def list_variance (l : List Float) : Float :=
  let mean := list_mean l
  let squared_diffs := l.map (fun x => (x - mean) * (x - mean))
  list_mean squared_diffs

/-- numpy.std: Standard deviation of array elements.

    Computes the standard deviation of all elements in the array.
    Requires a non-empty array since variance calculation needs the mean.

    The standard deviation is the square root of the variance, which measures
    the spread of the data around the mean.
-/
def numpy_std (a : Vector Float (n + 1)) : Id Float :=
  Id.pure (Float.sqrt (list_variance a.toList))

/-- Specification: numpy.std returns the standard deviation of all elements.

    Precondition: True (non-empty constraint is in the type)
    Postcondition: result = sqrt(variance) where variance = mean((x - mean)²)
-/
theorem numpy_std_spec (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    numpy_std a
    ⦃⇓result =>
      ⌜let mean := (List.sum (a.toList)) / Float.ofNat (n + 1)
      let variance := (List.sum (a.toList.map (fun x => (x - mean) * (x - mean)))) / Float.ofNat (n + 1)
      result = Float.sqrt variance⌝⦄ := by
  simp [numpy_std, List.length_toList, list_variance, list_mean]
  rfl