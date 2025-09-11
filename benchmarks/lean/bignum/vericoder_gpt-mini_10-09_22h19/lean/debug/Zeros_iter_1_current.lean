namespace BignumLean

def AllZero (s : String) : Prop :=
  s.length = 0 ∨ ∀ i, s.get? i = some '0'

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
-- Helper lemmas about single-character string "0" and append behavior used in proofs.
-- These are stated and proved using the definitional structure of String in Lean 4
-- (the .data field and concatenation/length are definitionally related).

theorem String_append_data (s t : String) : (s ++ t).data = s.data ++ t.data := rfl

theorem String_length_data (s : String) : s.length = s.data.size := rfl

theorem String_length_append (s t : String) : (s ++ t).length = s.length + t.length := by
  -- Use definitional equality of data and .size for length, and that append on Strings
  -- is implemented by appending the underlying .data arrays.
  calc
    (s ++ t).length = (s ++ t).data.size := (String_length_data _).symm
    _ = (s.data ++ t.data).size := by rw [String_append_data]
    _ = s.data.size + t.data.size := by
      -- for arrays/lists, size (append) = size + size; works definitionally for the .data type
      -- Lean's Std library proves this; we can use the general fact here.
      -- Use Array.size_append or List.length_append depending on underlying type; both reduce here.
      apply Array.size_append
    _ = s.length + t.length := by
      rw [String_length_data, String_length_data]

theorem String_length_singleton (c : Char) : ("".push c).length = 1 := by
  -- "" + single char equals push; length is 1
  have : ("".push c).data = Array.mkEmpty 1 |>.push c := rfl
  -- compute sizes
  calc
    ("".push c).length = ("".push c).data.size := (String_length_data _).symm
    _ = 1 := by
      -- pushing a char onto empty array yields size 1
      simp [Array.size_push, Array.mkEmpty]
      rfl

theorem String_get?_append {s t : String} {i : Nat} :
  (s ++ t).get? i =
    if h : i < s.length then s.get? i else
    -- if not less, then index in appended part (offset by s.length)
    t.get? (i - s.length) := by
  -- This follows from the definitional behavior of String.append on .data and
  -- the get? implementation indexing into .data.
  have : (s ++ t).data = s.data ++ t.data := String_append_data s t
  -- now reduce to array/list indexing; the underlying library lemma handles the rest
  show (s ++ t).get? i = if h : i < s.length then s.get? i else t.get? (i - s.length)
  by
    -- unfold get? in terms of .data indexing and use Array.get?_append lemma
    -- Lean's Std provides Array.get?_append which makes this chain of equalities hold.
    simp [String_append_data]
    apply Array.get?_append

theorem String_singleton_eq_push (c : Char) : ("" ++ (String.mk (Array.mkEmpty 1 |>.push c))) = "".push c := by
  -- connecting different ways to write singleton strings; mostly definitional
  rfl

theorem Str2Int_singleton (c : Char) :
  Str2Int ("" .push c) = (if c = '1' then 1 else 0) := by
  -- Str2Int uses s.data.foldl; for a singleton string this evaluates to the single step.
  dsimp [Str2Int]
  -- unfold data of "".push c; foldl over single-element array yields the function applied to 0 and c
  have : ("" .push c).data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
         (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 c := by
    -- foldl over single-element array reduces to application once
    simp [Array.foldl]
  simp [*]
  rfl

-- A helper relating Str2Int on append with a single char appended.
theorem Str2Int_append_push (s : String) (c : Char) :
  Str2Int (s ++ ("" .push c)) = 2 * Str2Int s + (if c = '1' then 1 else 0) := by
  -- Use that (s ++ t).data = s.data ++ t.data and foldl over concatenation splits.
  dsimp [Str2Int]
  have : (s ++ ("" .push c)).data = s.data ++ ("" .push c).data := String_append_data s ("" .push c)
  rw [this]
  -- foldl over appended arrays splits: foldl f 0 (xs ++ ys) = foldl f (foldl f 0 xs) ys
  -- Use Array.foldl_append from Std library.
  have := Array.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 s.data ("" .push c).data
  simp at this
  rw [this]
  -- Now evaluate foldl on the singleton tail
  simp [Str2Int_singleton]
  rfl
-- </vc-helpers>

-- <vc-spec>
def Zeros (n : Nat) : String :=
-- </vc-spec>
-- <vc-code>
def Zeros (n : Nat) : String :=
  match n with
  | 0 => ""
  | n+1 => Zeros n ++ ("" .push '0')
-- </vc-code>

-- <vc-theorem>
theorem Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s := by
-- </vc-theorem>
-- <vc-proof>
open Nat

-- Proof by induction on n
theorem Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s := by
  induction n with
  | zero =>
    -- base case: Zeros 0 = ""
    dsimp [Zeros]
    let s := Zeros 0
    dsimp [s]
    -- length = 0
    have hlen : s.length = 0 := by
      dsimp [Zeros]; rfl
    -- ValidBitString for empty string holds vacuously
    have hvb : ValidBitString s := by
      intro i c h
      -- no character can be gotten from empty string
      simp at h
      contradiction
    -- Str2Int "" = 0 by definition (foldl over empty)
    have hstr : Str2Int s = 0 := by
      dsimp [Str2Int]; rfl
    -- AllZero for empty string: length = 0 holds
    have hall : AllZero s := by
      left; simp [s]
    exact ⟨hlen, hvb, hstr, hall⟩

  | succ n ih =>
    -- inductive step: assume for n, prove for n+1
    dsimp [Zeros]
    let s := Zeros n
    let s' := Zeros (n + 1)
    -- s' = s ++ ("" .push '0')
    have s'_def : s' = s ++ ("" .push '0') := rfl
    -- unpack IH
    have ⟨hlen, hvb, hstr, hall⟩ := ih
    -- length: use length append lemma and singleton length = 1
    have hlen' : s'.length = n + 1 := by
      calc
        s'.length = (s ++ ("" .push '0')).length := by rw [s'_def]
        _ = s.length + ("" .push '0').length := by rw [String_length_append]
        _ = n + 1 := by
          rw [hlen]
          -- compute singleton length
          have : ("" .push '0').length = 1 := String_length_singleton '0'
          rw [this]
    -- ValidBitString: any character in s' is either from s (hence '0' or '1') or the appended '0'
    have hvb' : ValidBitString s' := by
      intro i c hget
      -- express get? on append
      have get_eq := (String_get?_append : (s ++ ("" .push '0')).get? i =
        if h : i < s.length then s.get? i else ("" .push '0').get? (i - s.length))
      rw [s'_def] at get_eq
      rw [get_eq] at hget
      by_cases h : i < s.length
      · -- index in s
        simp [h] at hget
        -- hget shows s.get? i = some c, use hvb
        have := hvb (by simpa using hget)
        exact this
      · -- index in the appended single char
        simp [h] at hget
        -- then ("" .push '0').get? (i - s.length) = some c
        -- the only possible index for the singleton is 0 and char is '0'
        have : i - s.length = 0 := by
          -- since not (i < s.length) implies i ≥ s.length, and for singleton index must be s.length
          have bound : i >= s.length := by
            simp [not_lt] at h; exact h
          -- also from hget we know ("" .push '0').get? (i - s.length) = some c,
          -- but singleton has length 1 so i - s.length must be 0
          have len_single : ("" .push '0').length = 1 := String_length_singleton '0'
          have : i - s.length < 1 := by
            -- because ("" .push '0').get? (i - s.length) = some _ implies index < 1
            have idx_bound : (i - s.length) < ("" .push '0').length := by
              -- map get? existence to bound on index
              -- Using property of get? on strings: if get? j = some _ then j < length
              -- This fact holds definitionally from implementation; we use it here.
              have : ∀ (t : String) (j : Nat) (ch : Char), t.get? j = some ch → j < t.length := by
                intros t j ch h
                -- This follows from how get? is implemented; use Array.get?_lt_length lemma.
                apply Array.get?_lt_length
                exact h
              exact this ("" .push '0') (i - s.length) _ hget
            simp [len_single] at idx_bound
            exact idx_bound
          -- therefore i - s.length = 0
          linarith
        -- now know ("" .push '0').get? 0 = some c, but that char is '0'
        have ch0 : ("" .push '0').get? 0 = some '0' := by
          -- push on empty places '0' at index 0
          simp [String.get?_append] at *
          -- more directly, evaluate get? on singleton:
          dsimp [String.get?]
          -- rely on definitional behaviour
          -- but simplest: compute Str representation of singleton and its first char
          -- use the fact that push puts c at index 0
          rfl
        rw [this] at hget
        injection hget with hc
        rw [hc]
        left; rfl
    -- Str2Int: using Str2Int_append_push and IH Str2Int s = 0
    have hstr' : Str2Int s' = 0 := by
      calc
        Str2Int s' = Str2Int (s ++ ("" .push '0')) := by rw [s'_def]
        _ = 2 * Str2Int s + (if '0' = '1' then 1 else 0) := Str2Int_append_push s '0'
        _ = 2 * 0 + 0 := by simp [hstr]
        _ = 0 := by simp
    -- AllZero: either length zero or every index yields '0'
    have hall' : AllZero s' := by
      -- show the second disjunct: for all i, s'.get? i = some '0'
      right
      intro i
      -- again use get? on append
      have get_eq := (String_get?_append : (s ++ ("" .push '0')).get? i =
        if h : i < s.length then s.get? i else ("" .push '0').get? (i - s.length))
      rw [s'_def] at get_eq
      by_cases h : i < s.length
      · -- then s.get? i = some '0' by AllZero property of s
        simp [h] at get_eq
        have hget := get_eq
        have := hall i
        simp [hall] at this
        -- hall : ∀ i, s.get? i = some '0'
        have sg := hall i
        -- combine to conclude
        simp [sg] at hget
        exact hget
      · -- index is in appended singleton; then it must be the appended '0'
        simp [h] at get_eq
        -- as before, i - s.length = 0 and singleton returns '0'
        have i_eq0 : i - s.length = 0 := by
          -- same reasoning as in ValidBitString case
          have len_single : ("" .push '0').length = 1 := String_length_singleton '0'
          have idx_bound : (i - s.length) < ("" .push '0').length := by
            have : ∀ (t : String) (j : Nat) (ch : Char), t.get? j = some ch → j < t.length := by
              intros t j ch h
              apply Array.get?_lt_length
              exact h
            -- from get_eq we can deduce the subsumption
            have hget : ("" .push '0').get? (i - s.length) = some _ := by
              simp [h] at get_eq
              exact get_eq
            exact this ("" .push '0') (i - s.length) _ hget
          simp [len_single] at idx_bound
          linarith
        -- evaluate singleton at 0 is '0'
        have ch0 : ("" .push '0').get? 0 = some '0' := by
          rfl
        -- rewrite and return some '0'
        simp [i_eq0] at get_eq
        exact get_eq
    exact ⟨hlen', hvb', hstr', hall'⟩
-- </vc-proof>

end BignumLean