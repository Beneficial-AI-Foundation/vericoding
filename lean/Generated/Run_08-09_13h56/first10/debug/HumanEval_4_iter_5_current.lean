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
lemma abs_sub_div_eq (x s : Rat) (n : Nat) (hn : (n : Rat) ≠ 0) :
  |x - s / n| = |x * n - s| / n := by
  have : x - s / n = (x * n - s) / n := by
    field_simp [hn]
    ring
  rw [this, abs_div]
  simp [abs_cast_nonneg]

-- LLM HELPER  
lemma list_sum_map_div (l : List Rat) (d : Rat) (hd : d ≠ 0) :
  (l.map (fun x => x / d)).sum = l.sum / d := by
  induction l with
  | nil => simp
  | cons a as ih => simp [List.sum_cons, add_div, ih]

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
    intro hpos
    exfalso
    simp at hpos h
    exact hpos h
  · -- non-empty case
    have hne : numbers ≠ [] := by
      intro heq
      rw [heq] at h
      simp at h
    have hlen : 0 < numbers.length := List.length_pos_of_ne_nil hne
    have hlen_ne_zero : (numbers.length : Rat) ≠ 0 := by
      rw [ne_eq, Nat.cast_eq_zero]
      exact ne_of_gt hlen
    
    let mean := numbers.sum / numbers.length
    let deviations := numbers.map (fun x => |x - mean|)
    let result := deviations.sum / numbers.length
    
    use result
    constructor
    · simp [mean, deviations, result]
    · intro _
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
        rw [list_sum_map_div _ _ hlen_ne_zero]