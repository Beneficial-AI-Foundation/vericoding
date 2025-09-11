namespace BignumLean

def AllZero (s : String) : Prop :=
  s.length = 0 ∨ ∀ i, s.get? i = some '0'

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
-- Helper lemmas about String/Array behaviors used in proofs.

theorem String_append_data (s t : String) : (s ++ t).data = s.data ++ t.data := rfl

theorem String_length_data (s : String) : s.length = s.data.size := rfl

theorem String_length_append (s t : String) : (s ++ t).length = s.length + t.length := by
  calc
    (s ++ t).length = (s ++ t).data.size := (String_length_data _).symm
    _ = (s.data ++ t.data).size := by rw [String_append_data]
    _ = s.data.size + t.data.size := by apply Array.size_append
    _ = s.length + t.length := by rw [String_length_data, String_length_data]

theorem String_push_data (s : String) (c : Char) : (s.push c).data = s.data.push c := rfl

theorem String_length_push (s : String) (c : Char) : (s.push c).length = s.length + 1 := by
  have : (s.push c).data = s.data.push c := String_push_data s c
  calc
    (s.push c).length = (s.push c).data.size := (String_length_data _).symm
    _ = (s.data.push c).size := by rw [this]
    _ = s.data.size + 1 := by apply Array.size_push
    _ = s.length + 1 := by rw [String_length_data]

theorem String_get?_push_at_length (s : String) (c : Char) : (s.push c).get? s.length = some c := by
  have : (s.push c).data = s.data.push c := String_push_data s c
  dsimp [String.get?]
  rw [this]
  -- use Array.get?_push which provides the element at index = original size
  apply Array.get?_push

theorem String_get?_lt_length (t : String) {j : Nat} {ch : Char} (h : t.get? j = some ch) : j < t.length := by
  -- underlying implementation delegates to Array.get?, so use Array lemma
  dsimp [String.get?] at h
  apply Array.get?_lt_length
  exact h

-- For indices strictly less than the original length, push does not affect get?
-- LLM HELPER
theorem String_get?_of_lt_push (s : String) (c : Char) {i : Nat} (h : i < s.length) :
  (s.push c).get? i = s.get? i := by
  have : (s.push c).data = s.data.push c := String_push_data s c
  dsimp [String.get?]
  rw [this]
  -- use Array.get?_push to get behavior for indices < original size
  apply Array.get?_push
  exact h

-- Str2Int on pushing a char: foldl over push equals folding then applying function to char
theorem Str2Int_push (s : String) (c : Char) :
  Str2Int (s.push c) = 2 * Str2Int s + (if c = '1' then 1 else 0) := by
  dsimp [Str2Int]
  have : (s.push c).data = s.data.push c := String_push_data s c
  rw [this]
  have h := Array.foldl_push (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 s.data c
  rw [h]
  rfl
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
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ (∀ i, i < s.length → s.get? i = some '0') := by
-- </vc-theorem>
-- <vc-proof>
open Nat

theorem Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ (∀ i, i < s.length → s.get? i = some '0') := by
  induction n with
  | zero =>
    dsimp [Zeros]
    let s := Zeros 0
    -- length = 0
    have hlen : s.length = 0 := by
      dsimp [Zeros]; rfl
    -- ValidBitString vacuously true for empty string
    have hvb : ValidBitString s := by
      intros i c h
      have : i < s.length := String_get?_lt_length h
      rw [hlen] at this
      exact False.elim (Nat.lt_irrefl _ this)
    -- Str2Int empty = 0
    have hstr : Str2Int s = 0 := by
      dsimp [Str2Int]; rfl
    -- all indices < length (none) satisfy property
    have hall : ∀ i, i < s.length → s.get? i = some '0' := by
      intro i hi
      cases Nat.not_lt_zero i hi
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
        _ = s.length + 1 := by apply String_length_push
        _ = n + 1 := by rw [hlen]

    -- ValidBitString
    have hvb' : ValidBitString s' := by
      intros i c hget
      rw [s'_def] at hget
      have ibound : i < s'.length := String_get?_lt_length hget
      -- with bound i < n+1 we have either i = n or i < n
      have : i ≤ n := by linarith [ibound]
      by_cases heq : i = n
      · -- i = n -> it's the pushed '0'
        have ch_at_len : (s.push '0').get? s.length = some '0' := String_get?_push_at_length s '0'
        rw [heq] at hget
        rw [ch_at_len] at hget
        injection hget with hc
        rw [hc]
        left; rfl
      · -- i < n
        have ilt : i < n := by
          have : i ≤ n := this
          have : ¬ (i = n) := by simp [heq]
          linarith
        -- relate get? on push to get? on s
        have eq := String_get?_of_lt_push s '0' (by linarith [hlt := ilt] : i < s.length)
        rw [eq] at hget
        exact hvb _ _ hget

    -- Str2Int: push relation and IH
    have hstr' : Str2Int s' = 0 := by
      calc
        Str2Int s' = Str2Int (s.push '0') := by rw [s'_def]
        _ = 2 * Str2Int s + (if '0' = '1' then 1 else 0) := by apply Str2Int_push
        _ = 2 * 0 + 0 := by simp [hstr]
        _ = 0 := by simp

    -- AllZero-like property: every position < length yields '0'
    have hall' : ∀ i, i < s'.length → s'.get? i = some '0' := by
      intro i hi
      dsimp at hi
      rw [s'_def]
      -- with bound i < n+1
      have : i ≤ n := by linarith [hi]
      by_cases heq : i = n
      · -- i = n -> pushed char
        rw [heq]
        exact String_get?_push_at_length s '0'
      · -- i < n
        have ilt : i < n := by
          have : i ≤ n := this
          have : ¬ (i = n) := by simp [heq]
          linarith
        -- use lemma to transfer get? from push to s, then apply IH's property
        have eq := String_get?_of_lt_push s '0' (by linarith [hlt := ilt] : i < s.length)
        rw [eq]
        exact hall i ilt

    exact ⟨hlen', hvb', hstr', hall'
-- </vc-proof>

end BignumLean