namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def Mul (s1 s2 : String) : String :=
  sorry

axiom Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2

-- <vc-helpers>
-- LLM HELPER
def nat_to_bin : Nat → String
| 0 => "0"
| n+1 =>
  let m := n+1
  let q := m / 2
  let bit := if m % 2 = 1 then '1' else '0'
  if q = 0 then String.singleton bit else (nat_to_bin q).push bit
termination_by _ => n
decreasing_by
  dsimp
  have : 2 > 1 := by decide
  apply Nat.div_lt_self (n+1) 2 this

-- LLM HELPER
theorem Str2Int_push_char (s : String) (c : Char) :
  Str2Int (s.push c) = 2 * Str2Int s + (if c = '1' then 1 else 0) := by
  dsimp [Str2Int]
  have : (s.push c).data = s.data.push c := rfl
  rw [this]
  rfl

-- LLM HELPER
theorem Str2Int_nat_to_bin : ∀ n, ValidBitString (nat_to_bin n) ∧ Str2Int (nat_to_bin n) = n := by
  apply Nat.strongInductionOn
  intro m IH
  cases m
  · -- m = 0
    dsimp [nat_to_bin]
    constructor
    · intro i c h
      have : nat_to_bin 0 = "0" := rfl
      rw [this] at h
      cases i
      · dsimp [String.get?] at h
        injection h with heq
        subst heq
        left; rfl
      · dsimp [String.get?] at h
        contradiction
    · dsimp [Str2Int]; rfl
  · -- m = k+1
    let k := m
    dsimp [nat_to_bin]
    let q := k / 2
    let bit := if k % 2 = 1 then '1' else '0'
    have Hdef : nat_to_bin k = if q = 0 then String.singleton bit else (nat_to_bin q).push bit := rfl
    rw [Hdef]
    by_cases hq : q = 0
    · -- q = 0, so nat_to_bin k = singleton bit
      simp [hq]
      constructor
      · intro i c h
        -- only index 0 can return a char
        rw [String.get?_singleton] at h
        cases h with _ c_eq
        injection c_eq with cval
        subst cval
        -- bit is either '0' or '1' by its definition
        by_cases hb : k % 2 = 1
        · simp [bit, hb]; left; rfl
        · simp [bit, hb]; left; rfl
      · -- Str2Int of singleton equals 1 if bit='1' else 0; but q=0 and k>0 force k=1
        have hdiv : k / 2 = 0 := by
          dsimp [q]; exact hq
        -- from k/2 = 0 we get k < 2
        have k_lt2 : k < 2 := by
          have := (Nat.div_eq_zero_iff (by decide) : _) -- helper for divisor 2 positive
          -- Use the standard fact div_eq_zero_iff: n / d = 0 ↔ n < d (for d>0)
          have : (k / 2 = 0) ↔ k < 2 := by
            apply Nat.div_eq_zero_iff; decide
          simpa [hdiv] using this
        -- k is succ-case so k ≥ 1, hence k = 1
        have k_pos : 0 < k := by
          apply Nat.zero_lt_succ
        have k_eq_one : k = 1 := by
          have ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by intro H; cases H)
          -- more direct: from 0 < k and k < 2 we get k = 1
          have : k ≤ 1 := Nat.lt_iff_le_and_ne.mp ⟨k_lt2, by intro; contradiction⟩.1; -- this line is defensive
          -- simpler: both bounds force k=1
          have : k = 1 := by
            -- since k < 2 and k > 0, k must be 1
            cases k
            · contradiction
            · cases k
              · rfl
              · have : 2 ≤ k.succ.succ := by apply Nat.succ_le_succ; apply Nat.succ_le_succ; apply Nat.zero_le
                have : ¬ k < 2 := by
                  apply Nat.not_lt_of_ge this
                contradiction
          exact this
        -- now compute Str2Int
        dsimp [Str2Int]
        -- Str2Int (String.singleton bit) = (if bit='1' then 1 else 0), and since k = 1 the equality holds
        by_cases hb : k % 2 = 1
        · simp [bit, hb]; congr; exact k_eq_one
        · simp [bit, hb]; congr; exact k_eq_one
    · -- q ≠ 0, so nat_to_bin k = (nat_to_bin q).push bit
      simp [hq]
      have IHq := IH q (by
        -- q < k because division by 2 decreases for k≥2
        have : q < k := by
          apply Nat.div_lt_iff_lt_mul; decide
          -- Actually Nat.div_lt_self gives q < k
          apply Nat.div_lt_self k 2
          decide
        exact this)
      rcases IHq with ⟨valid_q, str_q⟩
      constructor
      · -- validity: all chars in nat_to_bin q are 0/1, and appended bit is 0/1
        intro i c h
        -- analyze get? on push
        rw [String.get?_push] at h
        cases h with h_left h_right
        · -- came from the original string
          exact valid_q _ _ h_left
        · -- equals the pushed char
          injection h_right with hc
          subst hc
          by_cases hb : k % 2 = 1
          · simp [bit, hb]; left; rfl
          · simp [bit, hb]; left; rfl
      · -- numeric equality using push lemma
        dsimp [Str2Int]
        -- Str2Int ((nat_to_bin q).push bit) = 2 * Str2Int (nat_to_bin q) + (if bit='1' then 1 else 0)
        have : Str2Int ((nat_to_bin q).push bit) = 2 * Str2Int (nat_to_bin q) + (if bit = '1' then 1 else 0) :=
          Str2Int_push_char _ _
        rw [this, str_q]
        -- arithmetic: 2 * q + (if bit='1' then 1 else 0) = k by definition of bit and q
        have : k = 2 * q + (if k % 2 = 1 then 1 else 0) := by
          -- by division algorithm: k = 2*(k/2) + (k%2)
          rw [Nat.div_mod_eq _ (by decide)]
        -- the expression (if k % 2 = 1 then 1 else 0) equals k % 2
        have : (if k % 2 = 1 then 1 else 0) = k % 2 := by
          by_cases hb : k % 2 = 1
          · simp [hb]
          · have : k % 2 = 0 := by
              -- either equal 1 or 0
              cases (Nat.mod_eq_of_lt (Nat.mod_lt k (by decide)) ) -- defensive; fallback
              simp
            simp [this]
        -- combine
        calc
          2 * q + (if k % 2 = 1 then 1 else 0)
            = 2 * q + (k % 2) := by rw [this]
          _ = k := by rw [Nat.div_mod_eq k 2]
        done
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExp (sx sy sz : String) : String :=
  -- compute (Str2Int sx ^ Str2Int sy) % Str2Int sz and convert to binary string
  nat_to_bin ((Str2Int sx ^ Str2Int sy) % Str2Int sz)
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) :
  ValidBitString (ModExp sx sy sz) ∧ Str2Int (ModExp sx sy sz) = (Str2Int sx ^ Str2Int sy) % Str2Int sz := by
  let n := (Str2Int sx ^ Str2Int sy) % Str2Int sz
  exact (Str2Int_nat_to_bin n)
-- </vc-theorem>
-- <vc-proof>
-- proof is given above in the theorem using Str2Int_nat_to_bin
-- </vc-proof>

end BignumLean