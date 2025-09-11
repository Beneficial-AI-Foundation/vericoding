-- <vc-preamble>
def min_days (bloom_day : List Nat) (m k : Nat) : Int := sorry

def is_valid_result (bloom_day : List Nat) (m k : Nat) (result : Int) : Bool := sorry

def list_minimum (l : List Nat) : Nat := 
  match l with
  | [] => 0
  | (x::xs) => xs.foldl min x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_maximum (l : List Nat) : Nat := 
  match l with
  | [] => 0
  | (x::xs) => xs.foldl max x
-- </vc-definitions>

-- <vc-theorems>
theorem min_days_is_valid (bloom_day : List Nat) (m k : Nat) :
  m > 0 → k > 0 → is_valid_result bloom_day m k (min_days bloom_day m k) := sorry

theorem min_days_is_minimal (bloom_day : List Nat) (m k : Nat) :
  m > 0 → k > 0 → 
  min_days bloom_day m k ≠ -1 →
  ¬ is_valid_result bloom_day m k (min_days bloom_day m k - 1) := sorry

theorem min_days_within_bounds (bloom_day : List Nat) (m k : Nat) :
  m > 0 → k > 0 → bloom_day ≠ [] →
  min_days bloom_day m k ≠ -1 →
  min_days bloom_day m k ≥ list_minimum bloom_day ∧ 
  min_days bloom_day m k ≤ list_maximum bloom_day := sorry

theorem min_days_identical_values (bloom_day : List Nat) (m k : Nat) :
  m > 0 → k > 0 →
  (∀ x ∈ bloom_day, x = 1) →
  (min_days bloom_day m k = if bloom_day.length ≥ m * k then 1 else -1) := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_days [1, 10, 3, 10, 2] 3 1

/-
info: -1
-/
-- #guard_msgs in
-- #eval min_days [1, 10, 3, 10, 2] 3 2

/-
info: 12
-/
-- #guard_msgs in
-- #eval min_days [7, 7, 7, 7, 12, 7, 7] 2 3
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded