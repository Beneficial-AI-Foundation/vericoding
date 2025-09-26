-- <vc-preamble>

def power2 : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * power2 n

def ValidInput (n : Int) (lights : List Int) : Prop :=
  1 ≤ n ∧ n ≤ 10 ∧
  lights.length = power2 (Int.natAbs (n + 1)) - 2 ∧
  ∀ i, 0 ≤ i ∧ i < lights.length → 1 ≤ lights[i]! ∧ lights[i]! ≤ 100

partial def dfs_result (i n : Int) (a : List Int) : Int × Int :=
  if i ≥ Int.ofNat (power2 (Int.natAbs n)) then (0, 0)
  else
    let left := dfs_result (i * 2) n a
    let right := dfs_result (i * 2 + 1) n a
    let x1 := left.1; let m1 := left.2
    let x2 := right.1; let m2 := right.2
    if m1 + a[Int.natAbs (i * 2)]! < m2 + a[Int.natAbs (i * 2 + 1)]! then
      (x1 + x2 + m2 + a[Int.natAbs (i * 2 + 1)]! - m1 - a[Int.natAbs (i * 2)]!, m2 + a[Int.natAbs (i * 2 + 1)]!)
    else
      (x1 + x2 + m1 + a[Int.natAbs (i * 2)]! - m2 - a[Int.natAbs (i * 2 + 1)]!, m1 + a[Int.natAbs (i * 2)]!)

@[reducible, simp]
def solve_precond (n : Int) (lights : List Int) : Prop :=
  ValidInput n lights
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (lights : List Int) (h_precond : solve_precond n lights) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (lights : List Int) (result : Int) (h_precond : solve_precond n lights) : Prop :=
  result ≥ 0 ∧ result = (dfs_result 1 n ([0, 0] ++ lights)).1

theorem solve_spec_satisfied (n : Int) (lights : List Int) (h_precond : solve_precond n lights) :
    solve_postcond n lights (solve n lights h_precond) h_precond := by
  sorry
-- </vc-theorems>