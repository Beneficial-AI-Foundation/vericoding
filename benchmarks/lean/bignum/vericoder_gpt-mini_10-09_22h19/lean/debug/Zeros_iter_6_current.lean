namespace BignumLean

def AllZero (s : String) : Prop :=
  s.length = 0 ∨ ∀ i, s.get? i = some '0'

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
-- Helper lemmas about String/List behaviors used in proofs (adapted to String.data : List Char).

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

theorem List_get?_append_last {α} (l : List α) (x : α) : (l ++ [x]).get? l.length = some x := by
  induction l with
  | nil => simp [List.get?]
  | cons hd tl ih =>
    simp [List.get?]
    exact ih

theorem String_get?_push_at_length (s : String) (c : Char) : (s.push c).get? s.length = some c := by
  have : (s.push c).data = s.data ++ [c] := String_push_data s c
  dsimp [String.get?]
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
      have : i'.succ < tl.length + 1 := h
      have i'_lt : i' < tl.length := Nat.succ_lt_succ_iff.mp this
      simp [List.get?]
      apply ih
      exact i'_lt

theorem String_get?_of_lt_push (s : String) (c : Char) {i : Nat} (h : i < s.length) :
  (s.push c).get? i = s.get? i := by
  have : (s.push c).data = s.data ++ [c] := String_push_data s c
  dsimp [String.get?]
  -- convert h : i < s.length to i < s.data.length
  have h' : i < s.data.length := by
    rw [String_length_data] at h
    exact h
  rw [this]
  apply List_get?_of_lt_append_last
  exact h'

theorem String_get?_lt_length (t : String) {j : Nat} {ch : Char} (h : t.get? j = some ch) : j < t.length := by
  dsimp [String.get?] at h
  apply List.get?_lt_length
  exact h

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
      have : i < s.length := String_get?_lt_length h
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
      -- work on the pushed string
      rw [s'_def] at hget
      let ib := String_get?_lt_length hget
      -- ib : i < (s.push '0').length, convert to i < s.length + 1
      have ib' : i < s.length + 1 := by rw [String_length_push] at ib; exact ib
      have ile : i ≤ n := Nat.le_of_lt_succ ib'
      by_cases heq : i = n
      · -- i = n -> it's the pushed '0'
        -- convert hget index to s.length
        rw [heq, Eq.symm hlen] at hget
        have ch_at_len := String_get?_push_at_length s '0'
        rw [ch_at_len] at hget
        injection hget with hc
        left
        exact hc
      · -- i < n
        have ilt : i < n := by
          apply Nat.lt_of_le_and_ne ile
          exact heq
        have eq := String_get?_of_lt_push s '0' (by
          -- convert ilt : i < n to i < s.length using hlen
          have : i < s.length := by rw [hlen] at ilt; exact ilt
          exact this)
        rw [eq] at hget
        exact hvb _ _ hget

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
      -- work on representation s.push '0'
      rw [s'_def]
      -- hi : i < (s.push '0').length, convert to i < s.length + 1
      have hi' : i < s.length + 1 := by rw [String_length_push] at hi; exact hi
      have ile : i ≤ n := Nat.le_of_lt_succ hi'
      by_cases heq : i = n
      · -- i = n -> pushed char
        rw [heq, Eq.symm hlen]
        exact String_get?_push_at_length s '0'
      · -- i < n
        have ilt : i < n := by apply Nat.lt_of_le_and_ne ile; exact heq
        have eq := String_get?_of_lt_push s '0' (by
          have : i < s.length := by rw [hlen] at ilt; exact this
          exact this)
        rw [eq]
        exact hall i ilt

    exact ⟨hlen', hvb', hstr', hall'⟩
-- </vc-proof>

end BignumLean