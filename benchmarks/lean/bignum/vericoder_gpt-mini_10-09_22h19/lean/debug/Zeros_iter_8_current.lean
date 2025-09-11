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

theorem List_get?_append_last {α} (l : List α) (x : α) : (l ++ [x]).get? l.length = some x := by
  induction l with
  | nil => simp [List.get?]
  | cons hd tl ih =>
    simp [List.get?]
    exact ih

theorem List_get?_of_lt_append_last {α} (l : List α) (x : α) {i : Nat} (h : i < l.length) : (l ++ [x]).get? i = l.get? i := by
  induction l generalizing i with
  | nil =>
    contradiction
  | cons hd tl ih =>
    cases i with
    | zero => simp [List.get?]
    | succ i' =>
      simp [List.get?]
      apply ih
      exact h

theorem List_get?_lt_length {α} {l : List α} {j : Nat} {a : α} (h : l.get? j = some a) : j < l.length := by
  induction l generalizing j with
  | nil =>
    simp [List.get?] at h
    contradiction
  | cons hd tl ih =>
    cases j with
    | zero => simp [List.get?] at h; exact Nat.zero_lt_succ _
    | succ j' =>
      simp [List.get?] at h
      apply Nat.succ_lt_succ
      apply ih
      exact h

-- Convert between String.get? on a String.Pos and the underlying list access.
-- These lemmas use the String.Pos API (toNat and mk); they relate the two indexing views.
-- LLM HELPER
theorem String_get?_pos_to_data (s : String) (p : String.Pos) : s.get? p = s.data.get? p.toNat := by
  -- Unfolding String.get? reduces to the underlying list access; pattern matching the string exposes `.data`.
  cases s
  -- The kernel definition uses the data field; after cases this is just rfl.
  rfl

-- LLM HELPER
theorem String_get?_mk_nat (s : String) (i : Nat) : s.get? (String.Pos.mk i) = s.data.get? i := by
  -- mk and toNat satisfy toNat (mk i) = i, so reduce to the previous lemma.
  have : (String.Pos.mk i).toNat = i := by
    -- toNat (mk i) is definitionally i
    rfl
  calc
    s.get? (String.Pos.mk i) = s.data.get? ( (String.Pos.mk i).toNat ) := by rw [String_get?_pos_to_data]
    _ = s.data.get? i := by rw [this]

-- LLM HELPER
theorem String_get?_data_to_pos (s : String) (i : Nat) : s.data.get? i = s.get? (String.Pos.mk i) := by
  rw [String_get?_mk_nat]

theorem String_get?_lt_length (t : String) {p : String.Pos} {ch : Char} (h : t.get? p = some ch) : p.toNat < t.length := by
  -- reduce to list-level lemma
  have : t.data.get? p.toNat = some ch := by
    rw [String_get?_pos_to_data] at h
    exact h
  have := List_get?_lt_length this
  rwa [String_length_data] at this

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
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ (∀ i, i < s.length → s.get? (String.Pos.mk i) = some '0') :=
-- </vc-theorem>
-- <vc-proof>
open Nat

by
  induction
-- </vc-proof>

end BignumLean