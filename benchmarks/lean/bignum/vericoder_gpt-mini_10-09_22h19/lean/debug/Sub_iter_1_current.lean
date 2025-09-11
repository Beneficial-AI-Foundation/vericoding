namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
def nat_to_bin_list : Nat → List Char :=
  WellFounded.fix (measure_wf (id := Nat)) fun n rec =>
    match n with
    | 0 => []
    | Nat.succ k =>
      let prev := rec ((k + 1) / 2) (by
        have : 0 < k + 1 := Nat.succ_pos k
        exact Nat.div_lt_self this)
      let c := if (k + 1) % 2 = 1 then '1' else '0'
      prev ++ [c]

-- LLM HELPER
def nat_to_bin (n : Nat) : String := String.mk (nat_to_bin_list n)

-- LLM HELPER
theorem Str2Int_string_mk (l : List Char) : Str2Int (String.mk l) = l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 :=
  rfl

-- LLM HELPER
theorem nat_to_bin_valid (n : Nat) : ValidBitString (nat_to_bin n) := by
  -- strong induction on n
  apply Nat.strongInductionOn n
  intro m IH
  -- unfold definition via WellFounded.fix_eq to see structure
  have h_def := WellFounded.fix_eq (measure_wf (id := Nat)) (fun n rec =>
    match n with
    | 0 => []
    | Nat.succ k =>
      let prev := rec ((k + 1) / 2) (by
        have : 0 < k + 1 := Nat.succ_pos k
        exact Nat.div_lt_self this)
      let c := if (k + 1) % 2 = 1 then '1' else '0'
      prev ++ [c]) m
  dsimp [nat_to_bin] at h_def
  dsimp [nat_to_bin_list] at h_def
  -- consider cases on m
  cases m with
  | zero =>
    -- nat_to_bin_list 0 = [] so String.mk [] is empty string -> vacuously valid
    simp [h_def]
    intro i c h
    simp [String.get?, List.get?] at h
    contradiction
  | succ k =>
    -- expand nat_to_bin_list using h_def
    have : nat_to_bin_list (k + 1) = (nat_to_bin_list ((k + 1) / 2)) ++ [if (k + 1) % 2 = 1 then '1' else '0'] := by
      rw [← h_def]
    -- let s_prev be the string for previous part
    let prev := nat_to_bin ((k + 1) / 2)
-- </vc-helpers>

-- <vc-spec>
def Sub (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
def nat_to_bin_list : Nat → List Char :=
  WellFounded.fix (measure_wf (id := Nat)) fun n rec =>
    match n with
    | 0 => []
    | Nat.succ k =>
      let prev := rec ((k + 1) / 2) (by
        have : 0 < k + 1 := Nat.succ_pos k
        exact Nat.div_lt_self this)
      let c := if (k + 1) % 2 = 1 then '1' else '0'
      prev ++ [c]

-- LLM HELPER
def nat_to_bin (n : Nat) : String := String.mk (nat_to_bin_list n)

-- LLM HELPER
theorem Str2Int_string_mk (l : List Char) : Str2Int (String.mk l) = l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 :=
  rfl

-- LLM HELPER
theorem nat_to_bin_valid (n : Nat) : ValidBitString (nat_to_bin n) := by
  -- strong induction on n
  apply Nat.strongInductionOn n
  intro m IH
  -- unfold definition via WellFounded.fix_eq to see structure
  have h_def := WellFounded.fix_eq (measure_wf (id := Nat)) (fun n rec =>
    match n with
    | 0 => []
    | Nat.succ k =>
      let prev := rec ((k + 1) / 2) (by
        have : 0 < k + 1 := Nat.succ_pos k
        exact Nat.div_lt_self this)
      let c := if (k + 1) % 2 = 1 then '1' else '0'
      prev ++ [c]) m
  dsimp [nat_to_bin] at h_def
  dsimp [nat_to_bin_list] at h_def
  -- consider cases on m
  cases m with
  | zero =>
    -- nat_to_bin_list 0 = [] so String.mk [] is empty string -> vacuously valid
    simp [h_def]
    intro i c h
    simp [String.get?, List.get?] at h
    contradiction
  | succ k =>
    -- expand nat_to_bin_list using h_def
    have : nat_to_bin_list (k + 1) = (nat_to_bin_list ((k + 1) / 2)) ++ [if (k + 1) % 2 = 1 then '1' else '0'] := by
      rw [← h_def]
    -- let s_prev be the string for previous part
    let prev := nat_to_bin ((k + 1) / 2)
-- </vc-code>

end BignumLean