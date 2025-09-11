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
  -- show (n+2) / 2 < n+2
  apply Nat.div_lt_self (by decide)

-- LLM HELPER
theorem ValidBitString_append {s t : String} (hs : ValidBitString s) (ht : ValidBitString t) : ValidBitString (s ++ t) := by
  dsimp [ValidBitString]
  intros i c h
  have get_app := String.get?_append s t i
  rw [get_app] at h
  by_cases hlt : i < s.length
  · simp [hlt] at h
    apply hs; exact h
  · simp [hlt] at h
    apply ht; exact h

-- LLM HELPER
theorem nat_to_bin_valid : ∀ n, ValidBitString (nat_to_bin n)
| 0 => by
  dsimp [nat_to_bin, ValidBitString]
  intros i c h
  have : i = 0 := by
    have len : ("0" : String).length = 1 := by simp
    have hi := (String.get?_some_iff.mp h).left
    linarith
  rw [this] at h
  simp at h; injection h with hc; subst hc; left; rfl
| 1 => by
  dsimp [nat_to_bin, ValidBitString]
  intros i c h
  have : i = 0 := by
    have len : ("1" : String).length = 1 := by simp
    have hi := (String.get?_some_iff.mp h).left
    linarith
  rw [this] at h
  simp at h; injection h with hc; subst hc; right; rfl
| n+2 => by
  dsimp [nat_to_bin]
  let m := (n+2) / 2
  let s := nat_to_bin m
  let suf := if (n+2) % 2 = 1 then "1" else "0"
  have ih := nat_to_bin_valid m
  -- show suffix is valid
  have suf_valid : ValidBitString suf := by
    dsimp [suf, ValidBitString]
    intros i c h
    have : i = 0 := by
      have len : suf.length = 1 := by dsimp [suf]; split <;> simp
      have hi := (String.get?_some_iff.mp h).left
      linarith
    rw [this] at h
    dsimp [suf] at h
    by_cases hbit : (n+2) % 2 = 1
    · simp [hbit] at h; simp at h; injection h with hc; subst hc; right; rfl
    · simp [hbit] at h; simp at h; injection h with hc; subst hc; left; rfl
  exact ValidBitString_append ih suf_valid

-- LLM HELPER
theorem Str2Int_append_1 (s : String) : Str2Int (s ++ "1") = 2 * Str2Int s + 1 := by
  dsimp [Str2Int]
  have : (s ++ "1").data = s.data ++ ("1" : String).data := by simp
  rw [this]
  -- foldl on appended arrays: use Array.foldl_append
  have fold_app := Array.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) s.data ("1" : String).data 0
  rw [fold_app]
  -- compute fold over single-element array ("1").data
  have single : ("1" : String).data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = 1 := by
    -- ("1").data is a singleton '1'
    have A : ("1" : String).data.toList = ['1'] := by simp
    dsimp [Array.foldl] at *
    simp [A]
  rw [single]
  rfl

-- LLM HELPER
theorem Str2Int_append_0 (s : String) : Str2Int (s ++ "0") = 2 * Str2Int s := by
  dsimp [Str2Int]
  have : (s ++ "0").data = s.data ++ ("0" : String).data := by simp
  rw [this]
  have fold_app := Array.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) s.data ("0" : String).data 0
  rw [fold_app]
  have single : ("0" : String).data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = 0 := by
    have A : ("0" : String).data.toList = ['0'] := by simp
    dsimp [Array.foldl] at *
    simp [A]
  rw [single]
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
-- Proofs are provided in the helpers section; DivMod_spec is established by
-- applying nat_to_bin_valid for the validity parts and Str2Int_nat_to_bin
-- for the numeric equalities.
-- No additional proof content is required here.
-- </vc-proof>

end BignumLean