-- <vc-preamble>
def sum_playlist_duration (songs : List (Int × Int)) (n : Int) : Int :=
  if n ≤ 0 then 0
  else if n.toNat > songs.length then 0
  else 
    let rec helper (songs : List (Int × Int)) (n : Nat) : Int :=
      match n with
      | 0 => 0
      | Nat.succ m => 
        if m < songs.length then
          let song := songs[m]!
          song.1 * song.2 + helper songs m
        else 0
    helper songs n.toNat

def cumulative_duration_at_song (songs : List (Int × Int)) (song_idx : Int) : Int :=
  if song_idx < -1 then 0
  else if song_idx.toNat + 1 > songs.length then 0
  else
    let rec helper (songs : List (Int × Int)) (idx : Nat) : Int :=
      match idx with
      | 0 => if songs.length > 0 then let song := songs[0]!; song.1 * song.2 else 0
      | Nat.succ m => 
        if m < songs.length then
          let song := songs[m]!
          song.1 * song.2 + helper songs m
        else 0
    if song_idx == -1 then 0
    else helper songs song_idx.toNat

@[reducible, simp]
def solve_precond (n m : Int) (songs : List (Int × Int)) (queries : List Int) : Prop :=
  n ≥ 0 ∧ 
  m ≥ 0 ∧
  songs.length = n.toNat ∧
  queries.length = m.toNat ∧
  (∀ i, 0 ≤ i ∧ i < n → songs[i.toNat]!.1 > 0 ∧ songs[i.toNat]!.2 > 0) ∧
  (∀ i, 0 ≤ i ∧ i < m - 1 → queries[i.toNat]! < queries[(i+1).toNat]!) ∧
  (∀ i, 0 ≤ i ∧ i < m → queries[i.toNat]! ≥ 1) ∧
  (m = 0 ∨ queries[(m-1).toNat]! ≤ sum_playlist_duration songs n)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m : Int) (songs : List (Int × Int)) (queries : List Int) (h_precond : solve_precond n m songs queries) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m : Int) (songs : List (Int × Int)) (queries : List Int) (result : List Int) (h_precond : solve_precond n m songs queries) : Prop :=
  result.length = m.toNat ∧
  (∀ i, 0 ≤ i ∧ i < m → 1 ≤ result[i.toNat]! ∧ result[i.toNat]! ≤ n) ∧
  (∀ i, 0 ≤ i ∧ i < m → queries[i.toNat]! ≤ cumulative_duration_at_song songs (result[i.toNat]! - 1)) ∧
  (∀ i, 0 ≤ i ∧ i < m → result[i.toNat]! = 1 ∨ queries[i.toNat]! > cumulative_duration_at_song songs (result[i.toNat]! - 2))

theorem solve_spec_satisfied (n m : Int) (songs : List (Int × Int)) (queries : List Int) (h_precond : solve_precond n m songs queries) :
    solve_postcond n m songs queries (solve n m songs queries h_precond) h_precond := by
  sorry
-- </vc-theorems>