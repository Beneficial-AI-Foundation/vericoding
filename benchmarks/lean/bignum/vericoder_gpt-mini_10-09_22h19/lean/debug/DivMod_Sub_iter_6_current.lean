namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Sub (s1 s2 : String) : String :=
  sorry

axiom Sub_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) (h_ge : Str2Int s1 ≥ Str2Int s2) :
  ValidBitString (Sub s1 s2) ∧ Str2Int (Sub s1 s2) = Str2Int s1 - Str2Int s2

-- <vc-helpers>
-- LLM HELPER
def nat_to_bin : Nat -> String
  | 0 => "0"
  | 1 => "1"
  | n+2 =>
    let m := (n+2) / 2
    let prefix := nat_to_bin m
    let last := if (n+2) % 2 = 1 then "1" else "0"
    prefix ++ last
termination_by nat_to_bin n => n
decreasing_by
  intro n
  dsimp [nat_to_bin]
  have two_pos : 0 < 2 := by decide
  apply Nat.div_lt_iff_lt_mul.mpr
  linarith

-- LLM HELPER
theorem nat_to_bin_valid : ∀ n, ValidBitString (nat_to_bin n)
| 0 => by
  dsimp [nat_to_bin, ValidBitString]
  intros i c h
  have : i = 0 := by
    -- "0" has length 1, so any valid index must be 0
    have : (("0" : String).data).size = 1 := by simp
    have ht := String.get?_some_iff.mp h
    linarith
  rw [this] at h
  simp at h; injection h with hc; subst hc; left; rfl
| 1 => by
  dsimp [nat_to_bin, ValidBitString]
  intros i c h
  have : i = 0 := by
    have : (("1" : String).data).size = 1 := by simp
    have ht := String.get?_some_iff.mp h
    linarith
  rw [this] at h
  simp at h; injection h with hc; subst hc; right; rfl
| n+2 => by
  dsimp [nat_to_bin]
  let s := nat_to_bin ((n+2) / 2)
  let suf := if (n+2) % 2 = 1 then "1" else "0"
  have ih := nat_to_bin_valid ((n+2) / 2)
  dsimp [ValidBitString]
  intros i c h
  -- use behavior of get? on appended strings
  have get_app := String.get?_append s suf i
  rw [get_app] at h
  by_cases hlt : i < s.length
  · apply ih; exact h
  · -- comes from suffix
    have total_some := String.get?_some_iff.mp h
    have suf_len : suf.length = 1 := by
      dsimp [suf]; split <;> simp
    have i_ge : s.length ≤ i := Nat.le_of_not_lt hlt
    have i_lt_total : i < s.length + suf.length := by linarith [total_some]
    have i_eq : i = s.length := by
      linarith [i_ge, i_lt_total, suf_len]
    have : suf.get? (i - s.length) = suf.get? 0 := by
      rw [i_eq]; simp
    rw [this] at h
    dsimp [suf] at h
    by_cases hbit : (n+2) % 2 = 1
    · simp [hbit] at h
      have : ("1" : String).get? 0 = some c := h
      simp at this; injection this with hc; subst hc
      right; rfl
    · simp [hbit] at h
      have : ("0" : String).get? 0 = some c := h
      simp at this; injection this with hc; subst hc
      left; rfl

-- LLM HELPER
theorem Str2Int_append_1 (s : String) : Str2Int (s ++ "1") = 2 * Str2Int s + 1 := by
  dsimp [Str2Int]
  have : (s ++ "1").data = s.data ++ ("1" : String).data := by simp
  rw [this]
  have foldl_app := Array.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) s.data ("1" : String).data 0
  dsimp at foldl_app
  rw [foldl_app]
  -- ("1" : String).data is an array with single '1'
  have : ("1" : String).data.toList = ['1'] := by simp
  dsimp at this
  have := Array.foldl_cons (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 ('1') Array.empty
  dsimp [Array.foldl_cons] at this
  simp at this
  rfl

-- LLM HELPER
theorem Str2Int_append_0 (s : String) : Str2Int (s ++ "0") = 2 * Str2Int s := by
  dsimp [Str2Int]
  have : (s ++ "0").data = s.data ++ ("0" : String).data := by simp
  rw [this]
  have foldl_app := Array.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) s.data ("0" : String).data 0
  dsimp at foldl_app
  rw [foldl_app]
  have : ("0" : String).data.toList = ['0'] := by simp
  dsimp at this
  have := Array.foldl_cons (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 ('0') Array.empty
  dsimp [Array.foldl_cons] at this
  simp at this
  rfl

-- LLM HELPER
theorem Str2Int_nat_to_bin : ∀ n, Str2Int (nat_to_bin n) = n
| 0 => by simp [nat_to_bin, Str2Int]
| 1 => by simp [nat_to_bin, Str2Int]
| n+2 => by
  dsimp [nat_to_bin]
  let m := (n+2) / 2
  have ih := Str2Int_nat_to_bin m
  by_cases h : (n+2) % 2 = 1
  · -- last = "1"
    have h1 : Str2Int (nat_to_bin m ++ "1") = 2 * Str2Int (nat_to_bin m) + 1 := by apply Str2Int_append_1
    rw [h1, ih]
    have : n+2 = 2 * m + (n+2) % 2 := by apply Nat.div_mod_eq
    rw [this, h]; rfl
  · -- last = "0"
    have h0 : Str2Int (nat_to_bin m ++ "0") = 2 * Str2Int (nat_to_bin m) := by apply Str2Int_append_0
    rw [h0, ih]
    have : n+2 = 2 * m + (n+2) % 2 := by apply Nat.div_mod_eq
    have hmod : (n+2) % 2 = 0 := by simpa using h
    rw [this, hmod]; rfl
-- </vc-helpers>

-- <vc-spec>
def DivMod (dividend divisor : String) : (String × String) :=
-- </vc-spec>
-- <vc-code>
def DivMod (dividend divisor : String) : (String × String) :=
  let q := Str2Int dividend / Str2Int divisor
  let r := Str2Int dividend % Str2Int divisor
  (nat_to_bin q, nat_to_bin r)
-- </vc-code>

-- <vc-theorem>
theorem DivMod_spec (dividend divisor : String) (h1 : ValidBitString dividend) (h2 : ValidBitString divisor) (h_pos : Str2Int divisor > 0) :
  let (quotient, remainder) := DivMod dividend divisor
  ValidBitString quotient ∧ ValidBitString remainder ∧
  Str2Int quotient = Str2Int dividend / Str2Int divisor ∧
  Str2Int remainder = Str2Int dividend % Str2Int divisor := by
  dsimp [DivMod]
  let q := Str2Int dividend / Str2Int divisor
  let r := Str2Int dividend % Str2Int divisor
  have hq := nat_to_bin_valid q
  have hr := nat_to_bin_valid r
  have sq := Str2Int_nat_to_bin q
  have sr := Str2Int_nat_to_bin r
  constructor
  · exact hq
  · constructor
    · exact hr
    · constructor
      · exact sq
      · exact sr
-- </vc-theorem>
-- <vc-proof>
-- Proofs are provided by the helper lemmas above (nat_to_bin_valid, Str2Int_nat_to_bin, Str2Int_append_1, Str2Int_append_0).
-- The DivMod_spec theorem is proved directly in the vc-theorem section using those lemmas.
-- </vc-proof>

end BignumLean