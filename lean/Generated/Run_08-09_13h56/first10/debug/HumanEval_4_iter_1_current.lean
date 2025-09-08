import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (numbers: List Rat) : Rat :=
  if numbers.isEmpty then 0
  else
    let mean := numbers.sum / numbers.length
    let deviations := numbers.map (fun x => |x - mean|)
    deviations.sum / numbers.length

def problem_spec
-- function signature
(implementation: List Rat → Rat)
-- inputs
(numbers: List Rat) :=
-- spec
let spec (result: Rat):=
0 < numbers.length →
0 ≤ result ∧
result * numbers.length * numbers.length =
(numbers.map (fun x => |x * numbers.length - numbers.sum|)).sum;
-- program terminates
∃ result, implementation numbers = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma abs_div_eq (a b : Rat) (hb : b ≠ 0) : |a / b| = |a| / |b| := by
  rw [abs_div]

-- LLM HELPER
lemma sum_map_div (l : List Rat) (d : Rat) (hd : d ≠ 0) :
  (l.map (fun x => |x|)).sum / d = (l.map (fun x => |x| / d)).sum := by
  rw [List.sum_div]

-- LLM HELPER  
lemma abs_sub_div_eq (x s : Rat) (n : Nat) (hn : (n : Rat) ≠ 0) :
  |x - s / n| = |x * n - s| / n := by
  rw [← abs_div]
  congr 1
  field_simp
  ring

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  unfold implementation
  split_ifs with h
  · -- empty case
    simp [h]
    use 0
    simp
  · -- non-empty case
    push_neg at h
    have hlen : 0 < numbers.length := List.length_pos_of_ne_nil h
    have hlen_ne_zero : (numbers.length : Rat) ≠ 0 := by
      rw [ne_eq, Nat.cast_eq_zero]
      exact ne_of_gt hlen
    
    let mean := numbers.sum / numbers.length
    let deviations := numbers.map (fun x => |x - mean|)
    let result := deviations.sum / numbers.length
    
    use result
    constructor
    · simp [mean, deviations, result]
    · intro hpos
      constructor
      · -- result ≥ 0
        apply div_nonneg
        · apply List.sum_nonneg
          intro x hx
          simp at hx
          obtain ⟨y, _, rfl⟩ := hx
          exact abs_nonneg _
        · exact Nat.cast_nonneg _
      · -- main equality
        simp [result, deviations, mean]
        rw [div_mul_eq_mul_div, mul_div_assoc]
        congr 1
        rw [List.sum_map_div_distrib]
        congr 1
        ext x
        rw [abs_sub_div_eq]
        exact hlen_ne_zero