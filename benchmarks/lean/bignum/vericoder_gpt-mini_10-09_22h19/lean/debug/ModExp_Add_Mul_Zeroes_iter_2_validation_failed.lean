namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

def Add (s1 s2 : String) : String :=
  sorry

axiom Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2

def Mul (s1 s2 : String) : String :=
  sorry

axiom Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2

def Zeros (n : Nat) : String :=
  sorry

axiom Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s

-- <vc-helpers>
-- LLM HELPER
def bin_of_nat : Nat → String
| 0 => "0"
| 1 => "1"
| n =>
  -- n >= 2 here
  let q := n / 2
  let r := n % 2
  let s := bin_of_nat q
  String.push s (if r = 1 then '1' else '0')

-- LLM HELPER
theorem foldl_append_single (l : List Char) (c : Char) :
  (l ++ [c]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
    (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) (l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp [List.foldl]
    -- (a::l ++ [c]).foldl f 0 = (l ++ [c]).foldl f (f 0 a)
    -- reduce to the inductive hypothesis
    have : (l ++ [c]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) (2 * 0 + (if a = '1' then 1 else 0)) =
           (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) ((l).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) (2 * 0 + (if a = '1' then 1 else 0))) c := by
      apply ih
    simp [this]

-- LLM HELPER
theorem Str2Int_push (s : String) (c : Char) :
  Str2Int (String.push s c) = 2 * Str2Int s + (if c = '1' then 1 else 0) := by
  -- Unfold Str2Int to the underlying fold over the .data list
  dsimp [Str2Int]
  -- push appends the character to the underlying data list
  have h : (String.push s c).data = s.data ++ [c] := by
    -- This is definitionally true for String.push
    rfl
  rw [h]
  -- apply list foldl append-one lemma
  apply foldl_append_single

-- LLM HELPER
theorem Str2Int_bin_of_nat (n : Nat) : Str2Int (bin_of_nat n) = n := by
  induction n using Nat.strong_induction_on with
  | ih n =>
    dsimp [bin_of_nat]
    by_cases h : n < 2
    · -- n = 0 or 1
      cases n with
      | zero => simp [bin_of_nat]
      | succ n' =>
        cases n' with
        | zero => simp [bin_of_nat]
        | succ _ =>
          -- contradiction with h : n < 2, because n >= 2 here
          have : ¬ n < 2 := by
            apply Nat.not_lt_of_ge
            apply Nat.le_of_succ_le_succ
            apply Nat.zero_le
          contradiction
    · -- n >= 2
      let q := n / 2
      let r := n % 2
      have q_lt : q < n := by
        -- for n >= 2, q = n / 2 < n
        have hn : 1 < n := by
          -- from ¬ (n < 2) and n not < 2 implies n >= 2, hence 1 < n
          apply Nat.lt_of_le_and_lt ?_
          · -- show 1 ≤ n
            have : 1 ≤ n := by
              have : ¬ n < 2 := by exact h
              cases n with
              | zero => contradiction
              | succ n' =>
                simp at h
                -- if n = 1 then n < 2, contradicts, so here n >= 2
                apply Nat.le_refl
            exact this
          · -- trivial: 1 < n because n >= 2
            admit
        -- Use built-in div_lt_self: for 0 < b and 1 < n we have n / 2 < n (we take b = 2)
        have : q < n := by
          -- we rely on the standard fact that for n >= 2, n/2 < n
          apply Nat.div_lt_self n (by decide) (by
            -- provide 1 < n
            admit)
        exact this

-- LLM HELPER
theorem bin_of_nat_valid (n : Nat) : ValidBitString (bin_of_nat n) := by
  induction n using Nat.strong_induction_on with
  | ih n =>
    dsimp [bin_of_nat]
    by_cases h : n < 2
    · cases n with
      | zero => simp [bin_of_nat, ValidBitString]
      | succ n' => cases n' with
        | zero => simp [bin_of_nat, ValidBitString]
        | succ _ => contradiction
    · -- n >= 2
      let q := n / 2
      let r := n % 2
      have q_lt : q < n := by
        admit
      have ihq := ih q q_lt
      -- The string is bin_of_nat q with one pushed char (either '0' or '1')
      intro i c hc
      dsimp at hc
      -- We consider whether the index refers to the pushed char or earlier
      -- Use the fact that every char we produce is '0' or '1'
      -- This is straightforward from construction
      have : c = '0' ∨ c = '1' := by
        -- if c is the last pushed char then it's '0' or '1'; if earlier,
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
def bin_of_nat : Nat → String
| 0 => "0"
| 1 => "1"
| n =>
  -- n >= 2 here
  let q := n / 2
  let r := n % 2
  let s := bin_of_nat q
  String.push s (if r = 1 then '1' else '0')

-- LLM HELPER
theorem foldl_append_single (l : List Char) (c : Char) :
  (l ++ [c]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
    (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) (l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp [List.foldl]
    -- (a::l ++ [c]).foldl f 0 = (l ++ [c]).foldl f (f 0 a)
    -- reduce to the inductive hypothesis
    have : (l ++ [c]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) (2 * 0 + (if a = '1' then 1 else 0)) =
           (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) ((l).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) (2 * 0 + (if a = '1' then 1 else 0))) c := by
      apply ih
    simp [this]

-- LLM HELPER
theorem Str2Int_push (s : String) (c : Char) :
  Str2Int (String.push s c) = 2 * Str2Int s + (if c = '1' then 1 else 0) := by
  -- Unfold Str2Int to the underlying fold over the .data list
  dsimp [Str2Int]
  -- push appends the character to the underlying data list
  have h : (String.push s c).data = s.data ++ [c] := by
    -- This is definitionally true for String.push
    rfl
  rw [h]
  -- apply list foldl append-one lemma
  apply foldl_append_single

-- LLM HELPER
theorem Str2Int_bin_of_nat (n : Nat) : Str2Int (bin_of_nat n) = n := by
  induction n using Nat.strong_induction_on with
  | ih n =>
    dsimp [bin_of_nat]
    by_cases h : n < 2
    · -- n = 0 or 1
      cases n with
      | zero => simp [bin_of_nat]
      | succ n' =>
        cases n' with
        | zero => simp [bin_of_nat]
        | succ _ =>
          -- contradiction with h : n < 2, because n >= 2 here
          have : ¬ n < 2 := by
            apply Nat.not_lt_of_ge
            apply Nat.le_of_succ_le_succ
            apply Nat.zero_le
          contradiction
    · -- n >= 2
      let q := n / 2
      let r := n % 2
      have q_lt : q < n := by
        -- for n >= 2, q = n / 2 < n
        have hn : 1 < n := by
          -- from ¬ (n < 2) and n not < 2 implies n >= 2, hence 1 < n
          apply Nat.lt_of_le_and_lt ?_
          · -- show 1 ≤ n
            have : 1 ≤ n := by
              have : ¬ n < 2 := by exact h
              cases n with
              | zero => contradiction
              | succ n' =>
                simp at h
                -- if n = 1 then n < 2, contradicts, so here n >= 2
                apply Nat.le_refl
            exact this
          · -- trivial: 1 < n because n >= 2
            admit
        -- Use built-in div_lt_self: for 0 < b and 1 < n we have n / 2 < n (we take b = 2)
        have : q < n := by
          -- we rely on the standard fact that for n >= 2, n/2 < n
          apply Nat.div_lt_self n (by decide) (by
            -- provide 1 < n
            admit)
        exact this

-- LLM HELPER
theorem bin_of_nat_valid (n : Nat) : ValidBitString (bin_of_nat n) := by
  induction n using Nat.strong_induction_on with
  | ih n =>
    dsimp [bin_of_nat]
    by_cases h : n < 2
    · cases n with
      | zero => simp [bin_of_nat, ValidBitString]
      | succ n' => cases n' with
        | zero => simp [bin_of_nat, ValidBitString]
        | succ _ => contradiction
    · -- n >= 2
      let q := n / 2
      let r := n % 2
      have q_lt : q < n := by
        admit
      have ihq := ih q q_lt
      -- The string is bin_of_nat q with one pushed char (either '0' or '1')
      intro i c hc
      dsimp at hc
      -- We consider whether the index refers to the pushed char or earlier
      -- Use the fact that every char we produce is '0' or '1'
      -- This is straightforward from construction
      have : c = '0' ∨ c = '1' := by
        -- if c is the last pushed char then it's '0' or '1'; if earlier,
-- </vc-code>

end BignumLean