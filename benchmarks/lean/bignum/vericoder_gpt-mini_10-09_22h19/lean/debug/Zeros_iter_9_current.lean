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
    -- (hd :: tl ++ [x]).get? (tl.length + 1) reduces to (tl ++ [x]).get? tl.length
    simp [List.get?]
    exact ih

theorem List_get?_of_lt_append_last {α} (l : List α) (x : α) {i : Nat} (h : i < l.length) : (l ++ [x]).get? i = l.get? i := by
  induction l generalizing i with
  | nil => contradiction
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

-- LLM HELPER
theorem String_get?_pos_to_data (s : String) (p : String.Pos) : s.get? p = s.data.get? p.toNat := by
  cases s
  -- After deconstructing s, the definition of `get?` uses the `.data` field; rfl suffices.
  rfl

-- LLM HELPER
theorem String_get?_mk_nat (s : String) (i : Nat) : s.get? (String.Pos.mk i) = s.data.get? i := by
  -- String.Pos.mk i has toNat = i definitionally.
  have : (String.Pos.mk i).toNat = i := by rfl
  calc
    s.get? (String.Pos.mk i) = s.data.get? ( (String.Pos.mk i).toNat ) := by rw [String_get?_pos_to_data]
    _ = s.data.get? i := by rw [this]

-- LLM HELPER
theorem String_get?_data_to_pos (s : String) (i : Nat) : s.data.get? i = s.get? (String.Pos.mk i) := by
  rw [String_get?_mk_nat]

theorem String_get?_lt_length (t : String) {p : String.Pos} {ch : Char} (h : t.get? p = some ch) : p.toNat < t.length := by
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
  induction n with
  | zero =>
    -- Zeros 0 = ""
    dsimp [Zeros]
    -- construct the conjunction components
    constructor
    -- length = 0
    . simp [String_length_data]
    -- ValidBitString and Str2Int and all-zero indices
    . constructor
      -- ValidBitString: vacuously true for empty string
      . intros i c h
        simp [String.get?] at h
        contradiction
      . constructor
        -- Str2Int "" = 0
        . dsimp [Str2Int]; simp
        -- no indices less than 0
        . intros i h; exact False.elim (Nat.not_lt_zero i h)
  | succ n ih =>
    -- Let s := Zeros n, t := Zeros (n+1) = s.push '0'
    dsimp [Zeros]
    have ⟨hlen, hvalid, hstr, hall⟩ := ih
    let s := Zeros n
    let t := Zeros (n + 1)
    -- length
    constructor
    . calc
        t.length = (s.push '0').length := rfl
        _ = s.length + 1 := String_length_push s '0'
        _ = n + 1 := by rw [hlen]
    -- now prove ValidBitString, Str2Int = 0, and all indices zero.
    . constructor
      -- We'll first prove the "all indices are '0'" property and reuse it for ValidBitString.
      have all : ∀ i, i < t.length → t.get? (String.Pos.mk i) = some '0' := by
        intro i h
        -- t.length = s.length + 1
        have : t.length = s.length + 1 := by
          calc
            t.length = (s.push '0').length := rfl
            _ = s.length + 1 := String_length_push s '0'
        -- i < s.length + 1 implies i ≤ s.length
        have lei : i ≤ s.length := Nat.le_of_lt_succ (by rwa [this] at h)
        -- split into i = s.length or i < s.length
        cases (Nat.eq_or_lt_of_le lei) with
        | inl heq =>
          -- i = s.length: last element is '0'
          have : t.get? (String.Pos.mk i) = t.data.get? i := String_get?_mk_nat t i
          rw [String_push_data s '0'] at this
          -- replace i with s.length and s.length = s.data.length
          have ieq' : i = s.data.length := by
            rw [heq, String_length_data]
          rw [ieq'] at this
          -- now use List_get?_append_last
          have last := List_get?_append_last s.data '0'
          rw [← this] at last
          exact last
        | inr hlt =>
          -- i < s.length: use list-level lemma to reduce to s.get?
          have : t.get? (String.Pos.mk i) = t.data.get? i := String_get?_mk_nat t i
          rw [String_push_data s '0'] at this
          have : (s.data ++ ['0']).get? i = s.data.get? i := List_get?_of_lt_append_last s.data '0' hlt
          rw [this] at this
          -- convert back to string-level get? and use IH all zeros on s
          have : s.data.get? i = s.get? (String.Pos.mk i) := (String_get?_data_to_pos s i).symm
          rw [this] at this
          -- apply induction hypothesis all-zero property for s
          specialize hall i hlt
          exact hall
      -- Now ValidBitString: if get? returns some c, then c must be '0' (so '0' or '1' holds)
      . intros p c hp
        -- p is a String.Pos; convert to nat index
        have idx := String_get?_pos_to_data t p
        -- from hp and idx we know t.data.get? p.toNat = some c
        have getdata : t.get? p = some c := hp
        -- derive p.toNat < t.length by helper
        have lt := String_get?_lt_length t (by rwa [String_get?_pos_to_data] at getdata)
        -- use all to get that the character is '0'
        have chval := all p.toNat lt
        -- convert t.get? p to some '0' and compare
        have eq1 : t.get? p = some '0' := by
          -- t.get? p = t.get? (String.Pos.mk p.toNat) and both equal by String_get?_pos_to_data/mk lemma
          rw [String_get?_pos_to_data t p] at chval
          rw [String_get?_pos_to_data t p]
          exact chval
        rw [eq1] at hp
        simp at hp
        left; rfl
      -- Str2Int = 0
      . constructor
        . -- use Str2Int_push and hstr
          calc
            Str2Int t = 2 * Str2Int s + (if '0' = '1' then 1 else 0) := by rw [Str2Int_push s '0']
            _ = 2 * 0 + 0 := by rw [hstr]; simp
            _ = 0 := by simp
        -- finally the all-zero property
        . exact all
-- </vc-proof>

end BignumLean