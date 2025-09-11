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

-- LLM HELPER
theorem nat_to_bin_valid : ∀ n, ValidBitString (nat_to_bin n)
| 0 => by
  simp [nat_to_bin, ValidBitString]
  intros i c h
  -- "0" has length 1, but get? can only be some for i = 0; handle by contradiction
  have : (("0" : String).get? i) = some c := h
  have := String.get?_some_iff.mp (Option.isSome_of_eq_some this)
  -- i < 1 so i = 0, but then the char must be '0'
  have : i = 0 := by linarith [this]
  rw [this] at h
  simp at h; injection h; cc
| 1 => by
  simp [nat_to_bin, ValidBitString]
  intros i c h
  have : (("1" : String).get? i) = some c := h
  have := String.get?_some_iff.mp (Option.isSome_of_eq_some this)
  have : i = 0 := by linarith [this]
  rw [this] at h
  simp at h; injection h with hc; subst hc; left; rfl
| n+2 => by
  simp [nat_to_bin]
  let s := nat_to_bin ((n+2) / 2)
  let suf := if (n+2) % 2 = 1 then "1" else "0"
  have ih := nat_to_bin_valid ((n+2) / 2)
  intros i c h
  -- use behavior of get? on appended strings
  have get_app := String.get?_append s suf i
  rw [get_app] at h
  by_cases hlt : i < s.length
  · -- comes from prefix
    simp [hlt] at h
    exact ih h
  · -- comes from suffix: index refers to suf
    simp [hlt] at h
    -- from h we know (s ++ suf).get? i = some c, hence i < (s ++ suf).length
    have total_len_lt := String.get?_some_iff.mp (Option.isSome_of_eq_some h)
    -- suf.length = 1
    have suf_len : suf.length = 1 := by
      cases (n+2) % 2 = 1
      · simp [*]
      · simp [*]
    -- derive i = s.length
    have i_ge : i ≥ s.length := Nat.le_of_not_lt hlt
    have i_lt_total : i < s.length + suf.length := by linarith [total_len_lt]
    have i_eq : i = s.length := by
      linarith [i_ge, i_lt_total, suf_len]
    -- substitute into h to get suf.get? 0 = some c
    have : suf.get? (i - s.length) = suf.get? 0 := by
      rw [i_eq]; simp
    rw [this] at h
    -- now analyze suf
    dsimp [suf] at h
    by_cases hbit : (n+2) % 2 = 1
    · -- suf = "1"
      simp [hbit] at h
      have : ("1" : String).get? 0 = some c := h
      simp at this; injection this with hc; subst hc
      right; rfl
    · -- suf = "0"
      simp [hbit] at h
      have : ("0" : String).get? 0 = some c := h
      simp at this; injection this with hc; subst hc
      left; rfl

-- LLM HELPER
theorem Str2Int_append_1 (s : String) : Str2Int (s ++ "1") = 2 * Str2Int s + 1 := by
  simp [Str2Int]
  have : (s ++ "1").data = s.data ++ ("1" : String).data := by simp
  rw [this]
  -- foldl over appended arrays: use Array.foldl_append
  have foldl_app := Array.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) s.data ("1" : String).data 0
  dsimp at foldl_app
  rw [foldl_app]
  -- ("1" : String).data has a single char '1'
  have lst := ("1" : String).toList
  cases lst with
  | nil => simp at foldl_app; contradiction
  | cons c cs =>
    have : c = '1' := by simp
    simp [Array.foldl_cons, this]; rfl

-- LLM HELPER
theorem Str2Int_append_0 (s : String) : Str2Int (s ++ "0") = 2 * Str2Int s := by
  simp [Str2Int]
  have : (s ++ "0").data = s.data ++ ("0" : String).data := by simp
  rw [this]
  have foldl_app := Array.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) s.data ("0" : String).data 0
  dsimp at foldl_app
  rw [foldl_app]
  have lst := ("0" : String).toList
  cases lst with
  | nil => simp at foldl_app; contradiction
  | cons c cs =>
    have : c = '0' := by simp
    simp [Array.foldl_cons, this]; rfl

-- LLM HELPER
theorem Str2Int_nat_to_bin : ∀ n, Str2Int (nat_to_bin n) = n
| 0 => by simp [nat_to_bin, Str2Int]
| 1 => by simp [nat_to_bin, Str2Int]
| n+2 => by
  simp [nat_to_bin]
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
-- Proofs are provided in the helper lemmas above (nat_to_bin_valid, Str2Int_nat_to_bin, etc.)
-- and the DivMod_spec theorem is proved directly above using those lemmas.
-- </vc-proof>

end BignumLean