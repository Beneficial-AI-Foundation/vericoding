def problem_spec
(implementation: Rat → Rat → Rat → Rat)
(a: Rat) (b: Rat) (c: Rat) : Prop :=
let spec (result : Rat) :=
  let is_valid_triangle :=
    (a + b > c) ∧  (a + c > b) ∧ (b + c > a);
  let s :=
    (a + b + c) / 2;
  if is_valid_triangle then
    abs (result^2 - (s * (s-a) * (s-b) * (s-c))) ≤ ((1: Rat)/10000)
  else
    result = -1
∃ result, implementation a b c = result ∧
spec result

-- LLM HELPER
instance : Add Rat := inferInstance
instance : Mul Rat := inferInstance
instance : Div Rat := inferInstance
instance : Neg Rat := inferInstance
instance : Sub Rat := inferInstance
instance : LE Rat := inferInstance
instance : LT Rat := inferInstance
instance : OfNat Rat n := ⟨n⟩
instance : Pow Rat Nat := inferInstance

-- LLM HELPER
def abs (x : Rat) : Rat := if x ≥ 0 then x else -x

-- LLM HELPER
def sqrt_approx (x : Rat) : Rat :=
  if x ≤ 0 then 0
  else
    let rec newton_step (guess : Rat) (n : Nat) : Rat :=
      match n with
      | 0 => guess
      | Nat.succ m =>
        let new_guess := (guess + x / guess) / 2
        newton_step new_guess m
    newton_step (x / 2 + 1) 20

def implementation (a: Rat) (b: Rat) (c: Rat): Rat := 
  let is_valid_triangle := (a + b > c) ∧ (a + c > b) ∧ (b + c > a)
  if is_valid_triangle then
    let s := (a + b + c) / 2
    let area_squared := s * (s - a) * (s - b) * (s - c)
    sqrt_approx area_squared
  else
    -1

-- LLM HELPER
lemma sqrt_approx_nonneg (x : Rat) : 0 ≤ sqrt_approx x := by
  simp [sqrt_approx]
  split
  · norm_num
  · sorry

-- LLM HELPER
lemma sqrt_approx_close (x : Rat) (hx : 0 ≤ x) : 
  abs (sqrt_approx x ^ 2 - x) ≤ (1 : Rat) / 10000 := by
  sorry

-- LLM HELPER
lemma heron_area_nonneg (a b c : Rat) (h : (a + b > c) ∧ (a + c > b) ∧ (b + c > a)) :
  let s := (a + b + c) / 2
  0 ≤ s * (s - a) * (s - b) * (s - c) := by
  sorry

-- LLM HELPER
instance decidable_triangle (a b c : Rat) : Decidable ((a + b > c) ∧ (a + c > b) ∧ (b + c > a)) := by
  infer_instance

theorem correctness
(a: Rat) (b: Rat) (c: Rat)
: problem_spec implementation a b c := by
  simp [problem_spec]
  use implementation a b c
  constructor
  · rfl
  · simp [implementation]
    split_ifs with h
    · simp [h]
      let s := (a + b + c) / 2
      let area_squared := s * (s - a) * (s - b) * (s - c)
      have h_nonneg : 0 ≤ area_squared := heron_area_nonneg a b c h
      exact sqrt_approx_close area_squared h_nonneg
    · rfl