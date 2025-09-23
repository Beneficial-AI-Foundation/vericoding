-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_stone_positions (s : String) : List Nat := sorry

theorem stone_positions_length 
  (s : String) 
  (h : s.all (fun c => c = 'l' ∨ c = 'r')) 
  (h2 : s.length > 0) : 
  (get_stone_positions s).length = s.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem stone_positions_values_sorted 
  (s : String)
  (h : s.all (fun c => c = 'l' ∨ c = 'r'))
  (h2 : s.length > 0) :
  ∃ perm : List Nat, 
    get_stone_positions s = perm ∧ 
    List.range' 1 s.length = perm.reverse.reverse := sorry

theorem right_stones_come_first
  (s : String)
  (h : s.all (fun c => c = 'l' ∨ c = 'r'))
  (h2 : s.length > 0) :
  let right_pos := List.range s.length |>.map (fun i => i + 1) 
                   |>.filter (fun i => s.data.get! (i-1) = 'r')
  let get_index (xs : List Nat) (x : Nat) := 
    match xs.indexOf? x with
    | some idx => idx
    | none => 0
  let right_idx := right_pos.map (fun p => get_index (get_stone_positions s) p)
  right_pos ≠ [] →
  (∀ i j, i < j → i ∈ right_idx → j ∈ right_idx → right_idx[i]! ≤ right_idx[j]!) ∧
  (∀ i ∈ right_idx, i < s.length - (s.data.filter (·='l')).length) := sorry

theorem left_stones_come_last_reverse
  (s : String)
  (h : s.all (fun c => c = 'l' ∨ c = 'r'))
  (h2 : s.length > 0) :
  let left_pos := List.range s.length |>.map (fun i => i + 1)
                  |>.filter (fun i => s.data.get! (i-1) = 'l')
  let get_index (xs : List Nat) (x : Nat) := 
    match xs.indexOf? x with
    | some idx => idx
    | none => 0
  let left_idx := left_pos.map (fun p => get_index (get_stone_positions s) p)
  left_pos ≠ [] →
  ∀ i j, i < j → i ∈ left_idx → j ∈ left_idx → left_idx[i]! ≥ left_idx[j]! := sorry
-- </vc-theorems>