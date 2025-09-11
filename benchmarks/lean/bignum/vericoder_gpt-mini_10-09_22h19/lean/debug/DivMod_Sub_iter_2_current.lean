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
| 0 => by simp [nat_to_bin, ValidBitString]
| 1 => by simp [nat_to_bin, ValidBitString]
| n@(_+2) =>
  have ih : ValidBitString (nat_to_bin (n / 2)) := nat_to_bin_valid (n / 2)
  simp [nat_to_bin]
  -- prefix ++ last consists of prefix (valid) followed by "0" or "1"
  intros i c h
  -- any character from prefix is valid by ih; any from the single-char suffix is '0' or '1'
  have : (nat_to_bin (n / 2) ++ (if n % 2 = 1 then "1" else "0")).get? i = some c := h
  -- We reason by cases whether index i is within the prefix or equals the final char
  have hlen := (nat_to_bin (n / 2)).length
  by
    cases Nat.decLe (i) hlen
    · -- i < hlen, character comes from prefix
      have : (nat_to_bin (n / 2)).get? i = some c := by
        -- get? for append: when i < prefix.length, it equals prefix.get? i
        simp [String.get?_append_left _ _ _ h] at this
        exact this
      exact ih this
    · -- i ≥ hlen, must be the final character (only possible when i = hlen and suffix length = 1)
      have : i = hlen := by
        have : (if n % 2 = 1 then "1" else "0").length = 1 := by
          simp
        -- for append, indices beyond prefix length but less than total length correspond into suffix
        have total_len : (nat_to_bin (n / 2) ++ (if n % 2 = 1 then "1" else "0")).length = hlen + 1 := by
          simp
        have lt := (String.get?_some_iff.1 h).1
        -- deduce i < hlen + 1 and i ≥ hlen, hence i = hlen
        have i_lt : i < hlen + 1 := by
          simp [total_len] at lt; exact lt
        have i_ge : hlen ≤ i := by
          apply Nat.le_of_not_lt; intro H; apply Nat.not_lt_of_ge hlen H; contradiction
        linarith
      -- now i = hlen, the character is the only char of suffix
      rw [this] at h
      -- compute the character
      simp at h
      cases (n % 2 = 1) <;> simp at h; simp; finish

-- LLM HELPER
theorem Str2Int_append_1 (s : String) : Str2Int (s ++ "1") = 2 * Str2Int s + 1 := by
  -- Unfold definitions and use foldl on appending a single char
  simp [Str2Int]
  -- work with underlying data arrays
  have : (s ++ "1").data = s.data ++ ("1" : String).data := by simp
  rw [this]
  -- foldl over appended arrays: foldl f (a ++ b) 0 = foldl f b (foldl f a 0)
  -- use general property of Array.foldl
  have foldl_append := Array.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) s.data ("1" : String).data 0
  dsimp [Str2Int] at foldl_append
  rw [foldl_append]
  -- now fold over the single-char array yields the desired formula
  -- compute foldl over single char '1'
  have : ("1" : String).data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) (s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0)
    = 2 * (s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) + 1 := by
    -- reduce the foldl on single char
    cases ("1" : String).toList with
    | nil => simp at foldl_append; contradiction
    | cons c _ =>
      simp [Array.foldl_cons] -- one step of foldl on single-element array
      -- character must be '1'
      have : c = '1' := by
        -- the string "1" must have the character '1'
        simp
      simp [this]
  exact this

-- LLM HELPER
theorem Str2Int_append_0 (s : String) : Str2Int (s ++ "0") = 2 * Str2Int s := by
  simp [Str2Int]
  have : (s ++ "0").data = s.data ++ ("0" : String).data := by simp
  rw [this]
  have foldl_append := Array.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) s.data ("0" : String).data 0
  dsimp [Str2Int] at foldl_append
  rw [foldl_append]
  cases ("0" : String).toList with
  | nil => simp at foldl_append; contradiction
  | cons c _ =>
    simp [Array.foldl_cons]
    have : c = '0' := by simp
    simp [this]

-- LLM HELPER
theorem Str2Int_nat_to_bin : ∀ n, Str2Int (nat_to_bin n) = n
| 0 => by simp [nat_to_bin, Str2Int]
| 1 => by simp [nat_to_bin, Str2Int]
| n@(_+2) =>
  -- nat_to_bin n = nat_to_bin (n / 2) ++ last, and use IH plus append lemmas
  have ih := Str2Int_nat_to_bin (n / 2)
  simp [nat_to_bin]
  by_cases h : n % 2 = 1
  · -- last = "1"
    have : Str2Int (nat_to_bin (n / 2) ++ "1") = 2 * Str2Int (nat_to_bin (n / 2)) + 1 := by
      apply Str2Int_append_1
    simp [this, ih]
    -- compute arithmetic: 2 * (n/2) + 1 = n for n≥2 depending on parity
    have : 2 * (n / 2) + 1 = n := by
      have m := Nat.div_mul_cancel (by
        have : n / 2 * 2 = n - (n % 2) := Nat.mul_div_cancel' _ (by decide)
        -- easier: use Nat.div_mod_eq_iff and proven facts
        have := Nat.div_mod_eq n 2
        linarith)  -- let linarith solve numeric identity
      -- fallback to simple arithmetic property
      have : n = 2 * (n / 2) + n % 2 := by apply Nat.div_mod_eq
      rw [this]; rw [h]; simp
    rw [this]; rfl
  · -- last = "0"
    have : Str2Int (nat_to_bin (n / 2) ++ "0") = 2 * Str2Int (nat_to_bin (n / 2)) := by
      apply Str2Int_append_0
    simp [this, ih]
    have : 2 * (n / 2) = n := by
      have : n % 2 = 0 := by simpa using h
      have := Nat.div_mod_eq n 2
      linarith
    rw [this]; rfl
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
  -- unfold DivMod and apply properties of nat_to_bin
  simp [DivMod]
  intro ⟨quotient, remainder⟩
  dsimp [quotient, remainder]
  let q := Str2Int dividend / Str2Int divisor
  let r := Str2Int dividend % Str2Int divisor
  have hq := nat_to_bin_valid q
  have hr := nat_to_bin_valid r
  have sq := Str2Int_nat_to_bin q
  have sr := Str2Int_nat_to_bin r
  simp [hq, hr, sq, sr]
  -- build the conjunction
  constructor
  · exact hq
  · constructor
    · exact hr
    · constructor
      · exact sq
      · exact sr
-- </vc-theorem>
-- <vc-proof>
-- (Proofs are provided inline in the theorem above; no separate proof body needed.)
-- </vc-proof>

end BignumLean