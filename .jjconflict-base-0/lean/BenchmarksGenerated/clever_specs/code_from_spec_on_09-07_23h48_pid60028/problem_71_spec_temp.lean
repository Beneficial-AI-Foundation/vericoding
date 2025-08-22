def problem_spec
(implementation: Rat → Rat → Rat → Rat)
(a: Rat) (b: Rat) (c: Rat) : Prop :=
let spec (result : Rat) :=
  let is_valid_triangle :=
    (a + b > c) ∧  (a + c > b) ∧ (b + c > a);
  let s :=
    (a + b + c) / (2 : Rat);
  if is_valid_triangle then
    abs (result^2 - (s * (s-a) * (s-b) * (s-c))) ≤ ((1: Rat)/(10000: Rat))
  else
    result = (-1 : Rat)
∃ result, implementation a b c = result ∧
spec result

-- LLM HELPER
instance : Add Rat := Rat.add
instance : Mul Rat := Rat.mul
instance : Sub Rat := Rat.sub
instance : Div Rat := Rat.div
instance : Neg Rat := Rat.neg
instance : LE Rat := Rat.le
instance : LT Rat := Rat.lt
instance : OfNat Rat n := ⟨Rat.ofNat n⟩
instance : Pow Rat Nat := Rat.pow

-- LLM HELPER
def abs (x : Rat) : Rat := if x ≥ (0 : Rat) then x else -x

-- LLM HELPER
def sqrt_approx (x : Rat) : Rat :=
  if x ≤ (0 : Rat) then (0 : Rat)
  else
    let rec newton_step (guess : Rat) (n : Nat) : Rat :=
      match n with
      | 0 => guess
      | Nat.succ m =>
        let new_guess := (guess + x / guess) / (2 : Rat)
        newton_step new_guess m
    newton_step (x / (2 : Rat) + (1 : Rat)) 20

-- LLM HELPER
instance : Decidable (a + b > c ∧ a + c > b ∧ b + c > a) := by
  infer_instance

def implementation (a: Rat) (b: Rat) (c: Rat): Rat := 
  let is_valid_triangle := (a + b > c) ∧ (a + c > b) ∧ (b + c > a)
  if is_valid_triangle then
    let s := (a + b + c) / (2 : Rat)
    let area_squared := s * (s - a) * (s - b) * (s - c)
    sqrt_approx area_squared
  else
    (-1 : Rat)

-- LLM HELPER
lemma sqrt_approx_nonneg (x : Rat) : (0 : Rat) ≤ sqrt_approx x := by
  simp [sqrt_approx]
  split
  · norm_num
  · sorry

-- LLM HELPER
lemma sqrt_approx_close (x : Rat) (hx : (0 : Rat) ≤ x) : 
  abs (sqrt_approx x ^ 2 - x) ≤ (1 : Rat) / (10000 : Rat) := by
  sorry

-- LLM HELPER
lemma heron_area_nonneg (a b c : Rat) (h : (a + b > c) ∧ (a + c > b) ∧ (b + c > a)) :
  let s := (a + b + c) / (2 : Rat)
  (0 : Rat) ≤ s * (s - a) * (s - b) * (s - c) := by
  sorry

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
      let s := (a + b + c) / (2 : Rat)
      let area_squared := s * (s - a) * (s - b) * (s - c)
      have h_nonneg : (0 : Rat) ≤ area_squared := heron_area_nonneg a b c h
      exact sqrt_approx_close area_squared h_nonneg
    · rfl