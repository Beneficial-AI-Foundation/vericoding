-- <vc-preamble>
def List.sum : List Nat → Nat
  | [] => 0
  | x::xs => x + (sum xs)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_required (player enemy : List Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_required_diff_cases {player enemy : List Nat} 
  (h : player.length ≥ 1 ∧ enemy.length ≥ 1) :
  let diff : Int := Int.ofNat player.sum - Int.ofNat enemy.sum
  match diff with
  | 0 => get_required player enemy = "Random" 
  | d => 
    if d > 5 then get_required player enemy = "Auto-win"
    else if d < -5 then get_required player enemy = "Auto-lose" 
    else if d = -5 then get_required player enemy = "Pray for a tie!"
    else if d < 0 then get_required player enemy = s!"(1..{6-d.toNat-1})"
    else get_required player enemy = s!"({6-d+1}..6)" :=
  sorry

theorem same_arrays_random {xs : List Nat} (h : xs.length ≥ 1) :
  get_required xs xs = "Random" :=
  sorry

theorem get_required_symmetry {xs ys : List Nat}
  (h : xs.length ≥ 1 ∧ ys.length ≥ 1) :
  (get_required xs ys = "Auto-win" → get_required ys xs = "Auto-lose") ∧
  (get_required xs ys = "Auto-lose" → get_required ys xs = "Auto-win") :=
  sorry

/-
info: 'Auto-win'
-/
-- #guard_msgs in
-- #eval get_required [8, 1] [3, 0]

/-
info: 'Random'
-/
-- #guard_msgs in
-- #eval get_required [4, 0] [4, 0]

/-
info: 'Pray for a tie!'
-/
-- #guard_msgs in
-- #eval get_required [7, 2] [6, 8]
-- </vc-theorems>