def problem_spec
(implementation: Nat → Nat)
(x : Nat) :=
let spec (result: Nat) :=
  ∃ x_list : List Nat, x_list.length = x ∧ x_list.all (fun i => i = x)
  ∧ x_list.sum = result
∃ result, implementation x = result ∧
spec result

def implementation (x : Nat) : Nat := x * x

-- LLM HELPER
lemma replicate_length (n : Nat) (a : Nat) : (List.replicate n a).length = n := by
  induction n with
  | zero => simp [List.replicate]
  | succ n ih => simp [List.replicate, ih]

-- LLM HELPER
lemma replicate_all (n : Nat) (a : Nat) : (List.replicate n a).all (fun i => i = a) = true := by
  induction n with
  | zero => simp [List.replicate]
  | succ n ih => simp [List.replicate, List.all_cons, ih]

-- LLM HELPER
lemma replicate_sum (n : Nat) (a : Nat) : (List.replicate n a).sum = n * a := by
  induction n with
  | zero => simp [List.replicate]
  | succ n ih => simp [List.replicate, List.sum_cons, ih, Nat.succ_mul]

theorem correctness
(x : Nat)
: problem_spec implementation x := by
  unfold problem_spec implementation
  use x * x
  constructor
  · rfl
  · use List.replicate x x
    constructor
    · exact replicate_length x x
    · constructor
      · exact replicate_all x x
      · exact replicate_sum x x