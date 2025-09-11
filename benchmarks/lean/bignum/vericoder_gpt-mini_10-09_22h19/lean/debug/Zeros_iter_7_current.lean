namespace BignumLean

def AllZero (s : String) : Prop :=
  s.length = 0 ∨ ∀ i, s.get? i = some '0'

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
theorem String_append_data (s t : String) : (s ++ t).data = s.data ++ t.data := rfl

theorem String_length_data (s : String) : s.length = s.data.length := rfl

theorem String_length_append (s t : String) : (s ++ t).length = s.length + t.length := by
  calc
    (s ++ t).length = (s ++ t).data.length := (String_length_data _).symm
    _ = (s.data ++ t.data).length := by rw [String_append_data]
    _ = s.data.length + t.data.length := by rw [List.length_append]
    _ = s.length + t.length := by rw [String_length_data, String_length_data]

theorem String_push_data (s : String) (c : Char) : (s.push c).data = s.data ++ [c] := rfl

theorem String_length_push (s : String) (c : Char) : (s.push c).length = s.length + 1 := by
  have : (s.push c).data = s.data ++ [c] := String_push_data s c
  calc
    (s.push c).length = (s.push c).data.length := (String_length_data _).symm
    _ = (s.data ++ [c]).length := by rw [this]
    _ = s.data.length + [c].length := by rw [List.length_append]
    _ = s.data.length + 1 := by simp
    _ = s.length + 1 := by rw [String_length_data]

-- Relate String.get? (indexing by Nat) to the underlying list get? on data.
theorem String_get?_eq_data_get? (s : String) (i : Nat) : s.get? i = s.data.get? i := by
  -- The implementation of String.get? uses the underlying data.get?; this unfolds to rfl.
  -- Use dsimp to expose the definition and then rfl.
  dsimp [String.get?]
  rfl

theorem List_get?_append_last {α} (l : List α) (x : α) : (l ++ [x]).get? l.length = some x := by
  induction l with
  | nil => simp [List.get?]
  | cons hd tl ih =>
    simp [List.get?]
    exact ih

theorem String_get?_push_at_length (s : String) (c : Char) : (s.push c).get? s.length = some c := by
  have : (s.push c).data = s.data ++ [c] := String_push_data s c
  -- rewrite the string get? to data.get? and reduce lengths
  rw [String_get?_eq_data_get? (s.push c) s.length]
  rw [this, String_length_data]
  apply List_get?_append_last

theorem List_get?_of_lt_append_last {α} (l : List α) (x : α) {i : Nat} (h : i < l.length) : (l ++ [x]).get? i = l.get? i := by
  induction l generalizing i with
  | nil =>
    simp [List.get?] at h
    cases h
  | cons hd tl ih =>
    cases i with
    | zero => simp [List.get?]
    | succ i' =>
      simp [List.get?]
      have : i'.succ < tl.length + 1 := h
      have i'_lt : i' < tl.length := Nat.succ_lt_succ_iff.mp this
      apply ih
      exact i'_lt

theorem String_get?_of_lt_push (s : String) (c : Char) {i : Nat} (h : i < s.length) :
  (s.push c).get? i = s.get? i := by
  have : (s.push c).data = s.data ++ [c] := String_push_data s c
  -- rewrite both sides to data.get? and use the list lemma
  rw [String_get?_eq_data_get? (s.push c) i]
  rw [String_get?_eq_data_get? s i]
  rw [this]
  apply List_get?_of_lt_append_last
  -- convert i < s.length to i < s.data.length
  rw [String_length_data] at h
  exact h

theorem List_get?_lt_length {α} {l : List α} {j : Nat} {a : α} (h : l.get? j = some a) : j < l.length := by
  induction l generalizing j with
  | nil =>
    simp [List.get?] at h
    contradiction
  | cons hd tl ih =>
    cases j with
    | zero => simp [List.get?] at h; apply Nat.zero_lt_succ
    | succ j' =>
      simp [List.get?] at h
      apply Nat.succ_lt_succ
      apply ih
      exact h

theorem String_get?_lt_length (t : String) {j : Nat} {ch : Char} (h : t.get? j = some ch) : j < t.length := by
  -- relate to data.get? and use the list lemma
  have : t.data.get? j = some ch := by
    rw [←String_get?_eq_data_get? t j] at h
    exact h
  have <|= List_get?_lt_length this
  -- convert list length to string length
  rwa [String_length_data] at this
  -- Note: above line won't be reached; better to do direct:
  exact (List_get?_lt_length this)
  -- but to ensure final goal uses string length:
  all_goals
    change j < t.data.length
    exact (List_get?_lt_length this)

theorem Str2Int_push (s : String) (c : Char) :
  Str2Int (s.push c) = 2 * Str2Int s + (if c = '1' then 1 else 0) := by
  dsimp [Str2Int]
  have : (s.push c).data = s.data ++ [c] := String_push_data s c
  rw [this]
  have h := List.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 s.data [c]
  rw [h]
  simp
-- </vc-helpers>

-- <vc-spec>
def Zeros (n : Nat) : String :=
-- </vc-spec>
-- <vc-code>
def Zeros (n : Nat) : String :=
  match n with
  | 0 => ""
  | n+1 => (Zeros n).push '0'
-- </vc-code>

-- <vc-theorem>
theorem Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ (∀ i, i < s.length → s.get? i = some '0') :=
-- </vc-theorem>
-- <vc-proof>
open Nat

by
  induction n with
  | zero =>
    dsimp [Zeros]
    let s := Zeros 0
    -- length = 0
    have hlen : s.length = 0 := by dsimp [Zeros]; rfl
    -- ValidBitString vacuously true for empty string
    have hvb : ValidBitString s := by
      intros i c h
      have : i < s.length := by
        -- rewrite to data.get? then use list lemma
        rw [←String_get?_eq_data_get? s i] at h
        have := List_get?_lt_length (by simpa using h)
        rw [String_length_data] at this
        exact this
      rw [hlen] at this
      exact False.elim (Nat.not_lt_zero _ this)
    -- Str2Int empty = 0
    have hstr : Str2Int s = 0 := by dsimp [Str2Int]; simp
    -- all indices < length (none) satisfy property
    have hall : ∀ i, i < s.length → s.get? i = some '0' := by
      intro i hi
      exact False.elim (Nat.not_lt_zero _ hi)
    exact ⟨hlen, hvb, hstr, hall⟩

  | succ n ih =>
    dsimp [Zeros]
    let s := Zeros n
    let s' := Zeros (n + 1)
    have s'_def : s' = s.push '0' := rfl
    have ⟨hlen, hvb, hstr, hall⟩ := ih
    -- length
    have hlen' : s'.length = n + 1 := by
      calc
        s'.length = (s.push '0').length := by rw [s'_def]
        _ = s.length + 1 := by rw [String_length_push]
        _ = n + 1 := by rw [hlen]

    -- ValidBitString
    have hvb' : ValidBitString s' := by
      intros i c hget
      -- rewrite s'.get? to data.get? for manipulation
      rw [s'_def] at hget
      rw [String_get?_eq_data_get? (s.push '0') i] at hget
      -- now (s.data ++ ['0']).get? i = some c
      by_cases hpos : i = s.data.length
      · -- i equals position of appended char
        have last := List_get?_append_last s.data ('0' : Char)
        rw [hpos] at last
        -- last : (s.data ++ ['0']).get? s.data.length = some '0'
        rw [←last] at hget
        injection hget with hc
        left
        exact hc
      · -- i < s.data.length
        have ilt : i < s.data.length := by
          have : i < s.data.length + 1 := by
            -- convert to string length context then back
            have := String_get?_lt_length (s.push '0') (by
              -- need a proof that (s.push '0').get? i = some c -> i < (s.push '0').length
              exact hget)
            -- use String_length_push to move between lengths
            rw [String_length_push] at this
            exact this
          -- now i ≤ s.data.length and not equal so i < s.data.length
          have ile := Nat.le_of_lt_succ this
          exact Nat.lt_of_le_and_ne ile hpos.symm
        -- use list lemma to get s.data.get? i
        have eq := List_get?_of_lt_append_last s.data ('0' : Char) (by
          -- convert ilt to ilt for list
          exact ilt)
        have : s.data.get? i = some c := by
          rw [←eq] at hget; exact hget
        -- convert s.data.get? i to s.get? i and apply IH hvb
        have hstr' : s.get? i = some c := by
          rw [String_get?_eq_data_get? s i] at this
          exact this
        exact hvb _ _ hstr'

    -- Str2Int: push relation and IH
    have hstr' : Str2Int s' = 0 := by
      calc
        Str2Int s' = Str2Int (s.push '0') := by rw [s'_def]
        _ = 2 * Str2Int s + (if '0' = '1' then 1 else 0) := by apply Str2Int_push
        _ = 2 * 0 + 0 := by rw [hstr]; simp
        _ = 0 := by simp

    -- AllZero-like property: every position < length yields '0'
    have hall' : ∀ i, i < s'.length → s'.get? i = some '0' := by
      intro i hi
      -- rewrite to data.get? and inspect position
      rw [s'_def]
      rw [String_get?_eq_data_get? (s.push '0') i]
      have : i < s.data.length + 1 := by
        -- convert hi : i < s'.length to list-length form
        rw [hlen'] at hi
        -- s'.length = n+1 and s.length = n, so i < s.length + 1
        have : s.length = n := by rw [hlen]
        rw [←this] at hi
        -- convert string length to data length
        rw [String_length_data] at hi
        exact hi
      by_cases heq : i = s.data.length
      · -- it's the appended char
        rw [heq]
        -- List_get?_append_last gives last char
        have last := List_get?_append_last s.data ('0' : Char)
        rw [last]
        rfl
      · -- i < s.data.length, reduce to original hall
        have ilt : i < s.data.length := by
          have ile := Nat.le_of_lt_succ this
          exact Nat.lt_of_le_and_ne ile (mt (congrArg (· - s.data.length) (eq.symm heq)) (by simp [heq]))
        have eq := List_get?_of_lt_append_last s.data ('0' : Char) (by exact ilt)
        have tmp : s.data.get? i = some '0' := by
          rw [←eq] at *
          -- from s.data.get? i = some '0' follows using hall on s (translate to s.get?)
          have sget := by
            have hh : s.get? i = s.data.get? i := by rw [String_get?_eq_data_get? s i]
            rw [hh] at hall
            exact hall
          -- better to directly use hall from IH:
          have : s.get? i = some '0' := hall i (by
            -- convert ilt to i < s.length using hlen
            rw [String_length_data] at ilt
            rw [hlen] at ilt
            exact ilt)
          rw [←String_get?_eq_data_get? s i] at this
          exact this
        -- now convert to s'.get?
        rw [eq]
        exact tmp

    exact ⟨hlen', hvb', hstr', hall'⟩
-- </vc-proof>

end BignumLean