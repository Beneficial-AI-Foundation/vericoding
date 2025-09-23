-- <vc-preamble>
def pow26 : Nat → Nat
  | 0 => 1
  | n + 1 => 26 * pow26 n

partial def string_to_base26 (s : String) : Nat :=
  if s.length = 0 then 0
  else ((s.get! ⟨0⟩).toNat - ('a').toNat) * pow26 (s.length - 1) + string_to_base26 (s.drop 1)

partial def base26_to_string (val : Nat) (k : Nat) : String :=
  if k = 1 then String.mk [Char.ofNat ((val % 26) + ('a').toNat)]
  else base26_to_string (val / 26) (k - 1) ++ String.mk [Char.ofNat ((val % 26) + ('a').toNat)]

def median_string (s : String) (t : String) (k : Int) : String :=
  let s_val := string_to_base26 s
  let t_val := string_to_base26 t
  let median_val := (s_val + t_val) / 2
  base26_to_string median_val k.natAbs

@[reducible, simp]
def solve_precond (k : Int) (s : String) (t : String) : Prop :=
  k ≥ 1 ∧
  s.length = k.natAbs ∧
  t.length = k.natAbs ∧
  (∀ i, 0 ≤ i ∧ i < k.natAbs → ('a') ≤ (s.get! ⟨i⟩) ∧ (s.get! ⟨i⟩) ≤ ('z')) ∧
  (∀ i, 0 ≤ i ∧ i < k.natAbs → ('a') ≤ (t.get! ⟨i⟩) ∧ (t.get! ⟨i⟩) ≤ ('z')) ∧
  s < t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (k : Int) (s : String) (t : String) (h_precond : solve_precond k s t) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (k : Int) (s : String) (t : String) (result : String) : Prop :=
  result.length = k.natAbs ∧
  (∀ i, 0 ≤ i ∧ i < k.natAbs → ('a') ≤ (result.get! ⟨i⟩) ∧ (result.get! ⟨i⟩) ≤ ('z')) ∧
  s ≤ result ∧ result ≤ t ∧
  result = median_string s t k

theorem solve_spec_satisfied (k : Int) (s : String) (t : String) (h_precond : solve_precond k s t) :
    solve_postcond k s t (solve k s t h_precond) := by
  sorry
-- </vc-theorems>