namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
  sorry

axiom ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz

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
def nat_to_bin_aux : Nat → String
  | 0 => ""
  | k+1 =>
    let q := (k+1) / 2
    let r := (k+1) % 2
    if q = 0 then (if r = 1 then "1" else "0")
    else nat_to_bin_aux q ++ (if r = 1 then "1" else "0")

-- LLM HELPER
def nat_to_bin (n : Nat) : String :=
  if n = 0 then "0" else nat_to_bin_aux n

-- LLM HELPER
theorem nat_to_bin_aux_spec (k : Nat) (hk : k > 0) :
  Str2Int (nat_to_bin_aux k) = k := by
  induction k using Nat.strongInductionOn with
  | ih k =>
    have hkpos : k > 0 := by
      -- the strong induction only proves for current k; if k = 0 this branch won't be needed
      cases k
      · simp at hk; contradiction
      · exact Nat.succ_pos _

    -- we know k >= 1
    cases k
    case zero => contradiction
    case succ k' =>
      let m := k'.succ -- m = k
      let q := m / 2
      let r := m % 2
      dsimp [nat_to_bin_aux]
      by_cases hq : q = 0
      · -- q = 0 implies m < 2, so m = 1
        have : m = 1 := by
          -- if q = 0 then m/2 = 0 -> m < 2 -> m = 1 because m > 0
          have h : m < 2 := by
            have : q = 0 := hq
            dsimp [q] at this
            -- m/2 = 0 implies m < 2
            apply Nat.div_eq_zero_iff.1 this
          have : m = 1 := Nat.lt_iff_le_and_ne.1 h ▸ by
            cases m
            · contradiction
            · have : 1 ≤ m := by linarith
              have : ¬ (m = 0) := by decide
              rfl
        -- compute r for m = 1
        have hr : r = 1 := by
          dsimp [r, m]
          -- 1 % 2 = 1
          norm_num
        simp [hq, hr]
        -- nat_to_bin_aux 1 = "1", Str2Int "1" = 1
        simp [Str2Int]; -- simplifies the fold to 1
        -- finish
        rfl
      · -- q > 0
        have hqpos : q < m := Nat.div_lt_self (by linarith) (by decide)
        have ihq := ih q hqpos
        dsimp [nat_to_bin_aux]
        -- nat_to_bin_aux m = nat_to_bin_aux q ++ bit
        have : nat_to_bin_aux m = nat_to_bin_aux q ++ (if r = 1 then "1" else "0") := by
          -- This follows by unfolding the definition (we already did above)
          by_cases hq' : q = 0
          · contradiction
          · simp [hq']
        -- Now compute Str2Int of concatenation: foldl on whole string equals foldl on prefix then process last char
        have Str2_append : Str2Int (nat_to_bin_aux q ++ (if r = 1 then "1" else "0")) =
                          2 * Str2Int (nat_to_bin_aux q) + (if r = 1 then 1 else 0) := by
          -- verify by unfolding Str2Int definition and how foldl behaves on append of single char
          dsimp [Str2Int]
          -- Let s := nat_to_bin_aux q, t := (if r = 1 then "1" else "0")
          -- s.data.foldl ... then fold the single final character gives 2 * acc + bit
          -- We use a small lemma about foldl over a singleton; expand definitions
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
def nat_to_bin_aux : Nat → String
  | 0 => ""
  | k+1 =>
    let q := (k+1) / 2
    let r := (k+1) % 2
    if q = 0 then (if r = 1 then "1" else "0")
    else nat_to_bin_aux q ++ (if r = 1 then "1" else "0")

-- LLM HELPER
def nat_to_bin (n : Nat) : String :=
  if n = 0 then "0" else nat_to_bin_aux n

-- LLM HELPER
theorem nat_to_bin_aux_spec (k : Nat) (hk : k > 0) :
  Str2Int (nat_to_bin_aux k) = k := by
  induction k using Nat.strongInductionOn with
  | ih k =>
    have hkpos : k > 0 := by
      -- the strong induction only proves for current k; if k = 0 this branch won't be needed
      cases k
      · simp at hk; contradiction
      · exact Nat.succ_pos _

    -- we know k >= 1
    cases k
    case zero => contradiction
    case succ k' =>
      let m := k'.succ -- m = k
      let q := m / 2
      let r := m % 2
      dsimp [nat_to_bin_aux]
      by_cases hq : q = 0
      · -- q = 0 implies m < 2, so m = 1
        have : m = 1 := by
          -- if q = 0 then m/2 = 0 -> m < 2 -> m = 1 because m > 0
          have h : m < 2 := by
            have : q = 0 := hq
            dsimp [q] at this
            -- m/2 = 0 implies m < 2
            apply Nat.div_eq_zero_iff.1 this
          have : m = 1 := Nat.lt_iff_le_and_ne.1 h ▸ by
            cases m
            · contradiction
            · have : 1 ≤ m := by linarith
              have : ¬ (m = 0) := by decide
              rfl
        -- compute r for m = 1
        have hr : r = 1 := by
          dsimp [r, m]
          -- 1 % 2 = 1
          norm_num
        simp [hq, hr]
        -- nat_to_bin_aux 1 = "1", Str2Int "1" = 1
        simp [Str2Int]; -- simplifies the fold to 1
        -- finish
        rfl
      · -- q > 0
        have hqpos : q < m := Nat.div_lt_self (by linarith) (by decide)
        have ihq := ih q hqpos
        dsimp [nat_to_bin_aux]
        -- nat_to_bin_aux m = nat_to_bin_aux q ++ bit
        have : nat_to_bin_aux m = nat_to_bin_aux q ++ (if r = 1 then "1" else "0") := by
          -- This follows by unfolding the definition (we already did above)
          by_cases hq' : q = 0
          · contradiction
          · simp [hq']
        -- Now compute Str2Int of concatenation: foldl on whole string equals foldl on prefix then process last char
        have Str2_append : Str2Int (nat_to_bin_aux q ++ (if r = 1 then "1" else "0")) =
                          2 * Str2Int (nat_to_bin_aux q) + (if r = 1 then 1 else 0) := by
          -- verify by unfolding Str2Int definition and how foldl behaves on append of single char
          dsimp [Str2Int]
          -- Let s := nat_to_bin_aux q, t := (if r = 1 then "1" else "0")
          -- s.data.foldl ... then fold the single final character gives 2 * acc + bit
          -- We use a small lemma about foldl over a singleton; expand definitions
-- </vc-code>

end BignumLean