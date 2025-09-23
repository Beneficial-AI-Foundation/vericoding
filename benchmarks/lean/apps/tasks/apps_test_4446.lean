-- <vc-preamble>
def ValidInput (n a b k : Int) (H : List Int) : Prop :=
  n > 0 ∧ a > 0 ∧ b > 0 ∧ k ≥ 0 ∧ H.length = n ∧ 
  ∀ i, 0 ≤ i ∧ i < H.length → H[i]! > 0

def ProcessHealthValues (H : List Int) (a b : Int) : List Int :=
  H.map (fun h => 
    let h_mod := h % (a + b)
    if h_mod = 0 then a + b else h_mod)

partial def CountKillableHelper (sorted_health : List Int) (a remaining_k index acc : Int) : Int :=
  if index ≥ sorted_health.length then 
    acc
  else
    let x := sorted_health[index.toNat]!
    if x ≤ a then
      CountKillableHelper sorted_health a remaining_k (index + 1) (acc + 1)
    else
      let needed_skips := (x + a - 1) / a - 1
      if remaining_k ≥ needed_skips then
        CountKillableHelper sorted_health a (remaining_k - needed_skips) (index + 1) (acc + 1)
      else
        CountKillableHelper sorted_health a remaining_k (index + 1) acc

def CountKillableMonsters (sorted_health : List Int) (a k : Int) : Int :=
  CountKillableHelper sorted_health a k 0 0

@[reducible, simp]
def solve_precond (n a b k : Int) (H : List Int) : Prop :=
  ValidInput n a b k H
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n a b k : Int) (H : List Int) (h_precond : solve_precond n a b k H) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n a b k : Int) (H : List Int) (result : Int) (h_precond : solve_precond n a b k H) : Prop :=
  0 ≤ result ∧ result ≤ n

theorem solve_spec_satisfied (n a b k : Int) (H : List Int) (h_precond : solve_precond n a b k H) :
    solve_postcond n a b k H (solve n a b k H h_precond) h_precond := by
  sorry
-- </vc-theorems>