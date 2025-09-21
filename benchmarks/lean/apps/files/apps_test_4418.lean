-- <vc-preamble>
@[reducible, simp]
def ValidInput (n : Int) (a : List Int) : Prop :=
  n ≥ 0 ∧ a.length = n ∧ ∀ i, 0 ≤ i ∧ i < a.length → a[i]! ∈ [4, 8, 15, 16, 23, 42]

def update_state (s : List Int) (ai : Int) (k : List Int) : List Int :=
  if ai = k[5]! ∧ s[5]! > 0 then s.set 6 (s[6]! + 1) |>.set 5 (s[5]! - 1)
  else if ai = k[4]! ∧ s[4]! > 0 then s.set 5 (s[5]! + 1) |>.set 4 (s[4]! - 1)
  else if ai = k[3]! ∧ s[3]! > 0 then s.set 4 (s[4]! + 1) |>.set 3 (s[3]! - 1)
  else if ai = k[2]! ∧ s[2]! > 0 then s.set 3 (s[3]! + 1) |>.set 2 (s[2]! - 1)
  else if ai = k[1]! ∧ s[1]! > 0 then s.set 2 (s[2]! + 1) |>.set 1 (s[1]! - 1)
  else if ai = k[0]! ∧ s[0]! > 0 then s.set 1 (s[1]! + 1) |>.set 0 (s[0]! - 1)
  else s

def process_array : List Int → List Int → List Int → Nat → List Int
  | s, a, k, index =>
    if index ≥ a.length then s
    else
      let ai := a[index]!
      let new_s := update_state s ai k
      process_array new_s a k (index + 1)

def number_of_complete_subsequences (n : Int) (a : List Int) : Int :=
  let k := [4, 8, 15, 16, 23, 42]
  let s := [n, 0, 0, 0, 0, 0, 0]
  let final_s := process_array s a k 0
  final_s[6]!

def number_of_complete_subsequences_partial (n : Int) (a : List Int) (k : List Int) (index : Int) : Int :=
  let s := [n, 0, 0, 0, 0, 0, 0]
  let partial_a := if index = 0 then [] else a.take index.toNat
  let final_s := process_array s partial_a k 0
  final_s[6]!

@[reducible, simp]
def solve_precond (n : Int) (a : List Int) : Prop :=
  ValidInput n a
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (a : List Int) (h_precond : solve_precond n a) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (a : List Int) (result : Int) (h_precond : solve_precond n a) : Prop :=
  0 ≤ result ∧ result ≤ n ∧ result = n - 6 * (number_of_complete_subsequences n a)

theorem solve_spec_satisfied (n : Int) (a : List Int) (h_precond : solve_precond n a) :
    solve_postcond n a (solve n a h_precond) h_precond := by
  sorry
-- </vc-theorems>