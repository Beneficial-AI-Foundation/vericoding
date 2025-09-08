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
lemma sum_map_div (l : List Rat) (d : Rat) (hd : d ≠ 0) :
  (l.map (fun x => |x|)).sum / d = (l.map (fun x => |x| / d)).sum := by
  rw [← List.sum_map_div_left]
  simp

-- LLM HELPER
lemma abs_sub_div_eq (x s : Rat) (n : Nat) (hn : (n : Rat) ≠ 0) :
  |x - s / n| = |x * n - s| / n := by
  rw [← abs_div]
  congr 1
  field_simp [hn]
  ring

-- LLM HELPER
lemma list_not_isEmpty_iff_ne_nil (l : List α) : l.isEmpty ≠ true ↔ l ≠ [] := by
  simp [List.isEmpty]

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  unfold implementation
  split_ifs with h
  · -- empty case
    use 0
    simp
  · -- non-empty case
    rw [list_not_isEmpty_iff_ne_nil] at h
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
        have h_eq : (numbers.map (fun x => |x - numbers.sum / ↑numbers.length|)).sum = 
                   (numbers.map (fun x => |x * ↑numbers.length - numbers.sum| / ↑numbers.length)).sum := by
          congr 1
          ext x
          exact abs_sub_div_eq x numbers.sum numbers.length hlen_ne_zero
        rw [h_eq]
        rw [← List.sum_map_div_left]
        simp