namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

def DivMod (dividend divisor : String) : (String × String) :=
  sorry

axiom DivMod_spec (dividend divisor : String) (h1 : ValidBitString dividend) (h2 : ValidBitString divisor) (h_pos : Str2Int divisor > 0) :
  let (quotient, remainder) := DivMod dividend divisor
  ValidBitString quotient ∧ ValidBitString remainder ∧
  Str2Int quotient = Str2Int dividend / Str2Int divisor ∧
  Str2Int remainder = Str2Int dividend % Str2Int divisor

def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
  sorry

axiom ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz

def Zeros (n : Nat) : String :=
  sorry

axiom Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s

-- <vc-helpers>
-- LLM HELPER
-- Convert a Nat to its binary string representation (MSB first).
def nat_to_bin : Nat → String
| 0     => "0"
| n + 1 =>
  let s := nat_to_bin (n / 2)
  let last := if n % 2 = 1 then "1" else "0"
  s ++ last

-- LEMMA: correctness of nat_to_bin
theorem nat_to_bin_spec : ∀ n, ValidBitString (nat_to_bin n) ∧ Str2Int (nat_to_bin n) = n
| 0 => by
  simp [nat_to_bin, ValidBitString, Str2Int]
  constructor
  · intro i c h; simp at h; contradiction
  · rfl
| n + 1 => by
  let q := (n + 1) / 2
  have hq : q < n + 1 := by
    apply Nat.div_lt_self; decide
  have IH := nat_to_bin_spec q
  let s := nat_to_bin q
  have s_def := IH.2
  simp [nat_to_bin]
  constructor
  · -- ValidBitString: s valid, and last is "0" or "1"
    intro i c h
    -- we reason by cases whether index points into s or the last char
    have : i < (s.length + 1) := by
      simp [String.length] at *
      exact by
        have : (s ++ (if n % 2 = 1 then "1" else "0")).length = s.length + 1 := by
          simp [String.length, String.append]
        simpa [this] using h
    -- now reason directly by unfolding String.append and String.get? is tedious;
    -- instead use the fact that nat_to_bin only contains '0'/'1'.
    -- From IH we know s is valid; the appended char is '0' or '1', so valid holds.
    cases (Decidable.em (i < s.length))
    · apply IH.1; -- element comes from s
      -- obtain the character equality by indexing into s; we can use the original hypothesis
      -- but here we only need that characters are '0' or '1', which IH gives.
      exact by
        have : s.get? i = (s.get? i) := rfl
        apply (IH.1)
        intro i' c' h'; exact h'
    · -- i = s
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
-- Convert a Nat to its binary string representation (MSB first).
def nat_to_bin : Nat → String
| 0     => "0"
| n + 1 =>
  let s := nat_to_bin (n / 2)
  let last := if n % 2 = 1 then "1" else "0"
  s ++ last

-- LEMMA: correctness of nat_to_bin
theorem nat_to_bin_spec : ∀ n, ValidBitString (nat_to_bin n) ∧ Str2Int (nat_to_bin n) = n
| 0 => by
  simp [nat_to_bin, ValidBitString, Str2Int]
  constructor
  · intro i c h; simp at h; contradiction
  · rfl
| n + 1 => by
  let q := (n + 1) / 2
  have hq : q < n + 1 := by
    apply Nat.div_lt_self; decide
  have IH := nat_to_bin_spec q
  let s := nat_to_bin q
  have s_def := IH.2
  simp [nat_to_bin]
  constructor
  · -- ValidBitString: s valid, and last is "0" or "1"
    intro i c h
    -- we reason by cases whether index points into s or the last char
    have : i < (s.length + 1) := by
      simp [String.length] at *
      exact by
        have : (s ++ (if n % 2 = 1 then "1" else "0")).length = s.length + 1 := by
          simp [String.length, String.append]
        simpa [this] using h
    -- now reason directly by unfolding String.append and String.get? is tedious;
    -- instead use the fact that nat_to_bin only contains '0'/'1'.
    -- From IH we know s is valid; the appended char is '0' or '1', so valid holds.
    cases (Decidable.em (i < s.length))
    · apply IH.1; -- element comes from s
      -- obtain the character equality by indexing into s; we can use the original hypothesis
      -- but here we only need that characters are '0' or '1', which IH gives.
      exact by
        have : s.get? i = (s.get? i) := rfl
        apply (IH.1)
        intro i' c' h'; exact h'
    · -- i = s
-- </vc-code>

end BignumLean