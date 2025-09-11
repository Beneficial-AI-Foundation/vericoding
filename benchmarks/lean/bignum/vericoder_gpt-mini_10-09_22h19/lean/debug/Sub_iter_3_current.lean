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
  apply Nat.strongInductionOn n
  intro m IH
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
  cases m with
  | zero =>
    rw [h_def]
    intro i c h
    simp [String.get?, List.get?] at h
    contradiction
  | succ k =>
    have list_eq : nat_to_bin_list (k + 1) = nat_to_bin_list ((k + 1) / 2) ++ [if (k + 1) % 2 = 1 then '1' else '0'] := by
      rw [← h_def]
    let prev := nat_to_bin ((k + 1) / 2)
    intro i ch h
    -- handle indices coming from appended list
    have : String.mk (nat_to_bin_list ((k + 1) / 2) ++ [if (k + 1) % 2 = 1 then '1' else '0']) = nat_to_bin (k + 1) := by
      rfl
    rw [← list_eq] at h
    -- analyze whether index is within prev or the last element
    simp only [String.get?_mk, List.get?_append] at h
    cases h with
    | inl hget =>
      apply IH ((k + 1) / 2) (by
        have : (k + 1) / 2 < k + 1 := by
          have : 0 < k + 1 := Nat.succ_pos k
          exact Nat.div_lt_self this
        exact this)
      -- reconstruct the corresponding get? on prev string
      simpa using hget
    | inr hlast =>
      -- the last element is either '0' or '1'
      cases hlast with
      | intro hidx hch =>
        -- index must be last element, so it's either '0' or '1' by construction
        simp [hch]
        simp [String.get?] at hch
        exact (Or.inr rfl) -- ch = '1' or '0' as needed
        -- (The above line is syntactic; we can conclude because we know the character is '0' or '1')
        -- But to satisfy the goal, we destruct hch and finish:
        all_goals
          cases (if (k + 1) % 2 = 1 then '1' else '0') <;> simp at hch; contradiction <;> simp; assumption

-- LLM HELPER
theorem nat_to_bin_str2int (n : Nat) : Str2Int (nat_to_bin n) = n := by
  apply Nat.strongInductionOn n
  intro m IH
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
  cases m with
  | zero =>
    rw [h_def, Str2Int_string_mk]
    simp [List.foldl]
  | succ k =>
    -- set up components
    let n := k + 1
    have list_eq : nat_to_bin_list n = nat_to_bin_list (n / 2) ++ [if n % 2 = 1 then '1' else '0'] := by
      rw [← h_def]
    have : Str2Int (nat_to_bin n) = (nat_to_bin_list (n / 2) ++ [if n % 2 = 1 then '1' else '0']).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
      rw [nat_to_bin, list_eq, Str2Int_string_mk]
    -- foldl on appended single element
    simp only [List.foldl_append] at this
    -- evaluate the fold on the last char
    set c := (if n % 2 = 1 then '1' else '0') with hc
    have h1 : Str2Int (nat_to_bin (n / 2)) = (n / 2) := IH (n / 2) (by
      have : (n / 2) < n := by
        have : 0 < n := Nat.succ_pos k
        exact Nat.div_lt_self this
      exact this)
    rw [← h1] at this
    -- now this is 2 * (n / 2) + (if c = '1' then 1 else 0)
    simp only [List.foldl, List.foldl_cons] at this
    -- simplify the last term: (if c = '1' then 1 else 0) equals n % 2
    have : (if (n % 2) = 1 then 1 else 0) = n % 2 := by
      -- n % 2 is either 0 or 1
      let r := n % 2
      have r
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
  apply Nat.strongInductionOn n
  intro m IH
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
  cases m with
  | zero =>
    rw [h_def]
    intro i c h
    simp [String.get?, List.get?] at h
    contradiction
  | succ k =>
    have list_eq : nat_to_bin_list (k + 1) = nat_to_bin_list ((k + 1) / 2) ++ [if (k + 1) % 2 = 1 then '1' else '0'] := by
      rw [← h_def]
    let prev := nat_to_bin ((k + 1) / 2)
    intro i ch h
    -- handle indices coming from appended list
    have : String.mk (nat_to_bin_list ((k + 1) / 2) ++ [if (k + 1) % 2 = 1 then '1' else '0']) = nat_to_bin (k + 1) := by
      rfl
    rw [← list_eq] at h
    -- analyze whether index is within prev or the last element
    simp only [String.get?_mk, List.get?_append] at h
    cases h with
    | inl hget =>
      apply IH ((k + 1) / 2) (by
        have : (k + 1) / 2 < k + 1 := by
          have : 0 < k + 1 := Nat.succ_pos k
          exact Nat.div_lt_self this
        exact this)
      -- reconstruct the corresponding get? on prev string
      simpa using hget
    | inr hlast =>
      -- the last element is either '0' or '1'
      cases hlast with
      | intro hidx hch =>
        -- index must be last element, so it's either '0' or '1' by construction
        simp [hch]
        simp [String.get?] at hch
        exact (Or.inr rfl) -- ch = '1' or '0' as needed
        -- (The above line is syntactic; we can conclude because we know the character is '0' or '1')
        -- But to satisfy the goal, we destruct hch and finish:
        all_goals
          cases (if (k + 1) % 2 = 1 then '1' else '0') <;> simp at hch; contradiction <;> simp; assumption

-- LLM HELPER
theorem nat_to_bin_str2int (n : Nat) : Str2Int (nat_to_bin n) = n := by
  apply Nat.strongInductionOn n
  intro m IH
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
  cases m with
  | zero =>
    rw [h_def, Str2Int_string_mk]
    simp [List.foldl]
  | succ k =>
    -- set up components
    let n := k + 1
    have list_eq : nat_to_bin_list n = nat_to_bin_list (n / 2) ++ [if n % 2 = 1 then '1' else '0'] := by
      rw [← h_def]
    have : Str2Int (nat_to_bin n) = (nat_to_bin_list (n / 2) ++ [if n % 2 = 1 then '1' else '0']).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
      rw [nat_to_bin, list_eq, Str2Int_string_mk]
    -- foldl on appended single element
    simp only [List.foldl_append] at this
    -- evaluate the fold on the last char
    set c := (if n % 2 = 1 then '1' else '0') with hc
    have h1 : Str2Int (nat_to_bin (n / 2)) = (n / 2) := IH (n / 2) (by
      have : (n / 2) < n := by
        have : 0 < n := Nat.succ_pos k
        exact Nat.div_lt_self this
      exact this)
    rw [← h1] at this
    -- now this is 2 * (n / 2) + (if c = '1' then 1 else 0)
    simp only [List.foldl, List.foldl_cons] at this
    -- simplify the last term: (if c = '1' then 1 else 0) equals n % 2
    have : (if (n % 2) = 1 then 1 else 0) = n % 2 := by
      -- n % 2 is either 0 or 1
      let r := n % 2
      have r
-- </vc-code>

end BignumLean