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
  -- show (n+2) / 2 < n+2; use general lemma Nat.div_lt_self with divisor = 2 (>1)
  apply Nat.div_lt_self (by decide)

-- LLM HELPER
theorem nat_to_bin_valid : ∀ n, ValidBitString (nat_to_bin n)
| 0 => by
  dsimp [nat_to_bin, ValidBitString]
  intros i c h
  -- "0" has length 1, so index must be 0
  have : i = 0 := by
    have len : (("0" : String).length) = 1 := by simp
    have hi : i < ("0" : String).length := by
      show i < 1
      have h' := h
      -- from get? = some _ we know index is < length
      exact (String.get?_some_iff.mp h').left
    linarith
  rw [this] at h
  simp at h; injection h with hc; subst hc; left; rfl
| 1 => by
  dsimp [nat_to_bin, ValidBitString]
  intros i c h
  have : i = 0 := by
    have len : (("1" : String).length) = 1 := by simp
    have hi : i < ("1" : String).length := by
      have h' := h
      exact (String.get?_some_iff.mp h').left
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
    -- from h and the get?_append equation we have suf.get? (i - s.length) = some c
    have suf_some : suf.get? (i - s.length) = some c := by
      -- get_app was: (s ++ suf).get? i = if i < s.length then s.get? i else suf.get? (i - s.length)
      -- since ¬(i < s.length), the RHS is suf.get? (i - s.length)
      rw [if_neg hlt] at h
      exact h
    -- suffix has length 1, so the only index giving some is 0
    have suf_len : suf.length = 1 := by
      dsimp [suf]; split <;> simp
    have k_lt : (i - s.length) < suf.length := by
      have : (i - s.length) < s.length + suf.length - s.length := by
        -- from suf_some we know index is < suf.length using get?_some_iff
        have tmp := (String.get?_some_iff.mp suf_some).left
        exact tmp
      simp at this; exact this
    have : i - s.length = 0 := by
      have : (i - s.length) < 1 := by rwa [suf_len] at k_lt
      have : i - s.length = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt this)
      exact this
    have ieq : i = s.length := by
      dsimp [ieq]; rw [Nat.sub_eq_iff_eq_add_of_le (Nat.le_of_not_gt (not_lt.mp hlt)).symm] at this
      -- simpler:
      have hle := Nat.le_of_not_lt hlt
      have : i = s.length + (i - s.length) := by
        apply Nat.add_sub_of_le hle
      rw [this]; simp [this]; exact (by
        have kz : i - s.length = 0 := by
          have : (i - s.length) < 1 := by
            rwa [suf_len] at k_lt
          exact Nat.eq_zero_of_le_zero (Nat.le_of_lt this)
        rw [kz]; simp)
    -- using suf content
    dsimp [suf] at suf_some
    by_cases hbit : (n+2) % 2 = 1
    · simp [hbit] at suf_some
      have : ("1" : String).get? 0 = some c := by
        rw [← this]; simp at suf_some; exact suf_some
      simp at this; injection this with hc; subst hc; right; rfl
    · simp [hbit] at suf_some
      have : ("0" : String).get? 0 = some c := by
        rw [← this]; simp at suf_some; exact suf_some
      simp at this; injection this with hc; subst hc; left; rfl

-- LLM HELPER
theorem Str2Int_append_1 (s : String) : Str2Int (s ++ "1") = 2 * Str2Int s + 1 := by
  dsimp [Str2Int]
  have : (s ++ "1").data = s.data ++ ("1" : String).data := by simp
  rw [this]
  -- use Array.foldl_append: foldl over appended arrays equals foldl over first and then over second
  have foldl_app := Array.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) s.data ("1" : String).data 0
  rw [foldl_app]
  -- process the single-element array ("1").data
  have single := fun i => by
    dsimp; simp
  -- compute fold over single element '1'
  have : ("1" : String).data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = 1 := by
    -- ("1" : String).data has one element '1'
    have A : ("1" : String).data.toList = ['1'] := by simp
    dsimp [Array.foldl] at *
    -- reduce by evaluating the fold
    simp [A]
  -- now combine: result is 2 * Str2Int s + 1
  simp [Str2Int] at *
  -- by calculation the final result follows
  have : s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 * 2 + 1 = 2 * Str2Int s + 1 := by
    rfl
  rw [this]; exact Eq.refl _

-- LLM HELPER
theorem Str2Int_append_0 (s : String) : Str2Int (s ++ "0") = 2 * Str2Int s := by
  dsimp [Str2Int]
  have : (s ++ "0").data = s.data ++ ("0" : String).data := by simp
  rw [this]
  have foldl_app := Array.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) s.data ("0" : String).data 0
  rw [foldl_app]
  have : ("0" : String).data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = 0 := by
    have A : ("0" : String).data.toList = ['0'] := by simp
    dsimp [Array.foldl] at *
    simp [A]
  simp [Str2Int] at *
  have : s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 * 2 = 2 * Str2Int s := by rfl
  rw [this]; exact Eq.refl _

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
-- The necessary proof lemmas are provided in the helpers section.
-- DivMod_spec is proved directly using nat_to_bin_valid and Str2Int_nat_to_bin.
-- No additional proof content required here.
-- </vc-proof>

end BignumLean