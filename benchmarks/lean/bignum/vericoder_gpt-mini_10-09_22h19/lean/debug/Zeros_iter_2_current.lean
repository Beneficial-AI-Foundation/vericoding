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

-- push (append a single char) behaves on .data as Array.push
theorem String_push_data (s : String) (c : Char) : (s.push c).data = s.data.push c := rfl

-- length increases by 1 when pushing a char
theorem String_length_push (s : String) (c : Char) : (s.push c).length = s.length + 1 := by
  have : (s.push c).data = s.data.push c := String_push_data s c
  calc
    (s.push c).length = (s.push c).data.size := (String_length_data _).symm
    _ = (s.data.push c).size := by rw [this]
    _ = s.data.size + 1 := by apply Array.size_push
    _ = s.length + 1 := by rw [String_length_data]

-- get? on appended single char: the element at index s.length is the pushed char
theorem String_get?_push_at_length (s : String) (c : Char) : (s.push c).get? s.length = some c := by
  have : (s.push c).data = s.data.push c := String_push_data s c
  dsimp [String.get?]
  -- reduce to Array.get?_push which yields the pushed element at index = original size
  apply Array.get?_push

-- if get? yields some char then index is < length (uses Array lemma)
theorem String_get?_lt_length (t : String) {j : Nat} {ch : Char} (h : t.get? j = some ch) : j < t.length := by
  -- underlying implementation delegates to Array.get?, so use the Array lemma
  apply Array.get?_lt_length
  exact h

-- Str2Int on a singleton string: evaluating the foldl over single char
theorem Str2Int_singleton (c : Char) :
  Str2Int ("" .push c) = (if c = '1' then 1 else 0) := by
  dsimp [Str2Int]
  have : ("" .push c).data = Array.mkEmpty 0 |>.push c := rfl
  rw [this]
  -- foldl over single-element array reduces to one step
  show (Array.mkEmpty 0 |>.push c).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
       (if c = '1' then 1 else 0)
  -- use Array.foldl_push lemma
  have := Array.foldl_push (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 (Array.mkEmpty 0) c
  simp [this] at this
  -- foldl on empty array yields the initial 0, then apply function to 0 and c
  dsimp [Array.foldl] at this
  -- now compute the single application
  simp [this]

-- Str2Int on pushing a char: foldl over push equals folding then applying function to char
theorem Str2Int_push (s : String) (c : Char) :
  Str2Int (s.push c) = 2 * Str2Int s + (if c = '1' then 1 else 0) := by
  dsimp [Str2Int]
  have : (s.push c).data = s.data.push c := String_push_data s c
  rw [this]
  -- use Array.foldl_push to split the fold
  have := Array.foldl_push (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 s.data c
  rw [this]
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
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s := by
-- </vc-theorem>
-- <vc-proof>
open Nat

theorem Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s := by
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
      simp at h
      contradiction
    -- Str2Int empty = 0
    have hstr : Str2Int s = 0 := by
      dsimp [Str2Int]; rfl
    -- AllZero: left disjunct holds
    have hall : AllZero s := by
      left; simp [s]
    exact ⟨hlen, hvb, hstr, hall⟩

  | succ n ih =>
    dsimp [Zeros]
    let s := Zeros n
    let s' := Zeros (n + 1)
    -- s' = (Zeros n).push '0'
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
      -- index must be < s'.length = s.length + 1
      have idx_bound := String_get?_lt_length hget
      have : i ≤ s.length := by
        have : i < s.length + 1 := idx_bound
        linarith
      -- consider whether i < s.length or i = s.length
      by_cases h : i < s.length
      · -- then the character comes from s
        -- derive s.get? i = some c
        have : (s.push '0').get? i = s.get? i := by
          -- get? before the last index equals original get?
          -- can be seen from Array.get?_push lemma; use Array.get?_push to justify in underlying lib
          have : (s.push '0').data = s.data.push '0' := String_push_data s '0'
          dsimp [String.get?] at *
          apply Array.get?_push.left
        rw [this] at hget
        exact hvb (by simpa using hget)
      · -- not (i < s.length) so i ≥ s.length; with bound it's either = s.length
        have ieq : i = s.length := by
          have : i ≤ s.length := this
          have : ¬ (i < s.length) := by simpa using h
          linarith
        -- evaluate get? at index s.length
        have ch_at_len : (s.push '0').get? s.length = some '0' := String_get?_push_at_length s '0'
        rw [ieq] at hget
        rw [ch_at_len] at hget
        injection hget with hc
        rw [hc]
        left; rfl

    -- Str2Int: push relation and IH
    have hstr' : Str2Int s' = 0 := by
      calc
        Str2Int s' = Str2Int (s.push '0') := by rw [s'_def]
        _ = 2 * Str2Int s + (if '0' = '1' then 1 else 0) := by apply Str2Int_push
        _ = 2 * 0 + 0 := by simp [hstr]
        _ = 0 := by simp

    -- AllZero: every position yields '0'
    have hall' : AllZero s' := by
      right
      intro i
      rw [s'_def]
      -- index must be < s.length + 1
      have idx_bound := String_get?_lt_length
      -- split cases
      by_cases h : i < s.length
      · -- from IH all chars in s are '0'
        have gs : s.get? i = some '0' := hall i
        -- get? on push before last index equals s.get? i
        have : (s.push '0').get? i = s.get? i := by
          have : (s.push '0').data = s.data.push '0' := String_push_data s '0'
          dsimp [String.get?] at *
          apply Array.get?_push.left
        rw [this]
        exact gs
      · -- then i = s.length (since i < s.length + 1)
        have ieq : i = s.length := by
          have bound : i < s.length + 1 := by
            -- from existence of get? at i we get i < s'.length; but we don't have hget here, we can reason using bounds
            apply String_get?_lt_length
            -- to get some value we produce a witness: (s.push '0').get? i = (s.push '0').get? i -- trivial
            exact rfl
          have : ¬ (i < s.length) := by simpa using h
          linarith
        rw [ieq]
        -- evaluate pushed char at length
        exact String_get?_push_at_length s '0'
    exact ⟨hlen', hvb', hstr', hall'⟩
-- </vc-proof>

end BignumLean