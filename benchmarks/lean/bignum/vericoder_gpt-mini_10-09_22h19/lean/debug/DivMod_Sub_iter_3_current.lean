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
  | n => -- n ≥ 2
    let prefix := nat_to_bin (n / 2)
    let last := if n % 2 = 1 then "1" else "0"
    prefix ++ last

-- LLM HELPER
theorem nat_to_bin_valid : ∀ n, ValidBitString (nat_to_bin n)
| 0 => by
  simp [nat_to_bin, ValidBitString]
  intros i c h
  simp at h; contradiction
| 1 => by
  simp [nat_to_bin, ValidBitString]
  intros i c h
  simp at h
  cases h; simp_all
| n@(_+2) => by
  let s := nat_to_bin (n / 2)
  let suf := if n % 2 = 1 then "1" else "0"
  have ih := nat_to_bin_valid (n / 2)
  simp [nat_to_bin]
  intros i c h
  -- use the behavior of get? on appended strings
  have : (s ++ suf).get? i = if i < s.length then s.get? i else suf.get? (i - s.length) := by
    exact String.get?_append s suf i
  dsimp at this
  have := Eq.symm this ▸ h
  by_cases hlt : i < s.length
  · -- comes from prefix
    simp [hlt] at this
    exact ih this
  · -- comes from suffix: must be index 0 in suffix (since suffix length = 1)
    have : suf.length = 1 := by
      cases n % 2 = 1
      · simp
      · simp
    have : i ≥ s.length := by
      apply Nat.le_of_not_lt; intro H; exact hlt H
    have total_len : (s ++ suf).length = s.length + suf.length := by simp
    have i_lt_total : i < s.length + suf.length := by
      have hsome := String.get?_some_iff.1 h
      exact hsome.1
    have i_eq : i = s.length := by
      linarith [this, i_lt_total, this]
    rw [i_eq] at this
    simp [this] at h
    -- now suffix is "0" or "1"
    dsimp [suf] at h
    cases n % 2 = 1
    · simp at h; cases h; simp; exact Or.inr rfl
    · simp at h; cases h; simp; exact Or.inl rfl

-- LLM HELPER
theorem Str2Int_append_1 (s : String) : Str2Int (s ++ "1") = 2 * Str2Int s + 1 := by
  simp [Str2Int]
  have : (s ++ "1").data = s.data ++ ("1" : String).data := by simp
  rw [this]
  have foldl_append := Array.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) s.data ("1" : String).data 0
  dsimp [Str2Int] at foldl_append
  rw [foldl_append]
  -- foldl over single-char array
  have lst := ("1" : String).toList
  cases lst with
  | nil => simp at foldl_append; contradiction
  | cons c cs =>
    have : c = '1' := by
      simp
    simp [Array.foldl_cons, this]

-- LLM HELPER
theorem Str2Int_append_0 (s : String) : Str2Int (s ++ "0") = 2 * Str2Int s := by
  simp [Str2Int]
  have : (s ++ "0").data = s.data ++ ("0" : String).data := by simp
  rw [this]
  have foldl_append := Array.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) s.data ("0" : String).data 0
  dsimp [Str2Int] at foldl_append
  rw [foldl_append]
  have lst := ("0" : String).toList
  cases lst with
  | nil => simp at foldl_append; contradiction
  | cons c cs =>
    have : c = '0' := by simp
    simp [Array.foldl_cons, this]

-- LLM HELPER
theorem Str2Int_nat_to_bin : ∀ n, Str2Int (nat_to_bin n) = n
| 0 => by simp [nat_to_bin, Str2Int]
| 1 => by simp [nat_to_bin, Str2Int]
| n@(_+2) => by
  let s := nat_to_bin (n / 2)
  have ih := Str2Int_nat_to_bin (n / 2)
  simp [nat_to_bin]
  by_cases h : n % 2 = 1
  · -- last = "1"
    have h1 : Str2Int (s ++ "1") = 2 * Str2Int s + 1 := by apply Str2Int_append_1
    rw [h1, ih]
    -- show 2 * (n / 2) + 1 = n
    have : n = 2 * (n / 2) + n % 2 := by apply Nat.div_mod_eq
    rw [this, h]; rfl
  · -- last = "0"
    have h0 : Str2Int (s ++ "0") = 2 * Str2Int s := by apply Str2Int_append_0
    rw [h0, ih]
    have : n = 2 * (n / 2) + n % 2 := by apply Nat.div_mod_eq
    have hmod : n % 2 = 0 := by simpa using h
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
  simp [DivMod]
  -- after unfolding, DivMod returns (nat_to_bin q, nat_to_bin r)
  intro ⟨quotient, remainder⟩
  dsimp [quotient, remainder]
  let q := Str2Int dividend / Str2Int divisor
  let r := Str2Int dividend % Str2Int divisor
  have hq := nat_to_bin_valid q
  have hr := nat_to_bin_valid r
  have sq := Str2Int_nat_to_bin q
  have sr := Str2Int_nat_to_bin r
  dsimp at hq hr sq sr
  -- assemble the conjunction
  constructor
  · exact hq
  · constructor
    · exact hr
    · constructor
      · exact sq
      · exact sr
-- </vc-theorem>
-- <vc-proof>
-- Proofs are provided inline in the theorem and helper lemmas above.
-- </vc-proof>

end BignumLean