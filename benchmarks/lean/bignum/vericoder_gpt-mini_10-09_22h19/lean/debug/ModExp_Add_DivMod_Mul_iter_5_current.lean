namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def Add (s1 s2 : String) : String :=
  sorry

axiom Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2

def DivMod (dividend divisor : String) : (String × String) :=
  sorry

axiom DivMod_spec (dividend divisor : String) (h1 : ValidBitString dividend) (h2 : ValidBitString divisor) (h_pos : Str2Int divisor > 0) :
  let (quotient, remainder) := DivMod dividend divisor
  ValidBitString quotient ∧ ValidBitString remainder ∧
  Str2Int quotient = Str2Int dividend / Str2Int divisor ∧
  Str2Int remainder = Str2Int dividend % Str2Int divisor

def Mul (s1 s2 : String) : String :=
  sorry

axiom Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2

-- <vc-helpers>
-- LLM HELPER
theorem Exp_int_add (x a b : Nat) : Exp_int x (a + b) = Exp_int x a * Exp_int x b := by
  induction b with
  | zero => simp [Exp_int]
  | succ b ih =>
    show Exp_int x (a + b + 1) = Exp_int x a * (x * Exp_int x b)
    calc
      Exp_int x (a + b + 1) = x * Exp_int x (a + b) := by simp [Exp_int]
      _ = x * (Exp_int x a * Exp_int x b) := by rw [ih]
      _ = (Exp_int x a) * (x * Exp_int x b) := by rw [mul_comm (Exp_int x a) (x * Exp_int x b)]; rfl

-- LLM HELPER
theorem Exp_int_two_mul (x n : Nat) : Exp_int x (2 * n) = Exp_int x n * Exp_int x n := by
  calc
    Exp_int x (2 * n) = Exp_int x (n + n) := by simp [Nat.mul_comm]
    _ = Exp_int x n * Exp_int x n := by rw [Exp_int_add x n n]

-- LLM HELPER
theorem nat_mul_mod_comm (a b m : Nat) : (a * b) % m = ((a % m) * (b % m)) % m := by
  -- This follows from repeated application of Nat.mul_mod
  calc
    (a * b) % m = ((a % m) * b) % m := by apply Nat.mul_mod
    _ = ((a % m) * (b % m)) % m := by
      -- apply Nat.mul_mod with a := (a % m) , b := (b % m) + m * (b / m)
      have : b = (b % m) + m * (b / m) := by apply Nat.mod_add_div
      rw [this]
      -- ((a% m) * ((b % m) + m * (b / m))) % m = ((a % m) * (b % m) + (a % m) * m * (b / m)) % m
      rw [mul_add, mul_assoc]
      -- terms with factor m vanish modulo m
      have : ((a % m) * (b % m) + (a % m) * m * (b / m)) % m = ((a % m) * (b % m)) % m := by
        rw [Nat.add_mul_mod_left]
      exact this

-- convenience lemma: Str2Int of the single-character "1" equals 1
-- LLM HELPER
theorem Str2Int_one : Str2Int "1" = 1 := by
  -- compute directly from definition
  show "1".data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = 1
  -- "1".data is ['1'], so foldl gives 2*0 + 1
  simp [String.data]; rfl
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExp (sx sy sz : String) : String :=
  let base0 := (DivMod sx sz).2
  let init : String × String := ("1", base0)
  let f := fun (st : String × String) (ch : Char) =>
    let r := st.1
    let b := st.2
    let prod := Mul r r
    let prod_mod := (DivMod prod sz).2
    let r' :=
      if ch = '1' then
        let tmp := Mul prod_mod b
        (DivMod tmp sz).2
      else
        prod_mod
    let b2 := (DivMod (Mul b b) sz).2
    (r', b2)
  (sy.data.foldl f init).1
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
  -- Proof will follow by induction on the list of bits of sy
  set x := Str2Int sx
  set m := Str2Int sz
  -- get info about initial reduction base0 := sx % sz
  have div0 := DivMod_spec sx sz hx hz hsz_gt1
  have ⟨_hq_valid, hb0_valid, _hq_val, hb0_val⟩ := div0
  let base0 := (DivMod sx sz).2
  -- define the folding function as in the implementation
  let init : String × String := ("1", base0)
  let f := fun (st : String × String) (ch : Char) =>
    let r := st.1
    let b := st.2
    let prod := Mul r r
    let prod_mod := (DivMod prod sz).2
    let r' :=
      if ch = '1' then
        let tmp := Mul prod_mod b
        (DivMod tmp sz).2
      else
        prod_mod
    let b2 := (DivMod (Mul b b) sz).2
    (r', b2)
  let l := sy.data

  -- We prove by induction on the processed prefix that the invariant holds:
  -- for a prefix list t of length k, the folded state (r,b) satisfies:
  --   ValidBitString r, ValidBitString b,
  --   Str2Int r = Exp_int x (value_of_prefix t) % m
  --   Str2Int b = Exp_int x (2^k) % m  (equivalently base exponent doubling)
  have IH : ∀ (t : List Char), 
    let st := t.foldl f init in
    ValidBitString st.1 ∧ ValidBitString st.2 ∧
    Str2Int st.1 = Exp_int x (t.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) % m ∧
    Str2Int st.2 = Exp_int x (2 ^ t.length) % m := by
    intro t
    induction t with
    | nil =>
      -- base case: no bits processed, state = init
      simp [init]
      constructor
      · -- ValidBitString "1"
        -- "1" is a single valid bit
        intro i c hc
        simp at hc
        cases hc
        subst hc
        simp
      constructor
      · -- base0 validity from DivMod_spec
        exact hb0_valid
      constructor
      · -- Str2Int "1" = 1 and Exp_int x 0 = 1, so equality holds
        have : t.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = 0 := by simp
        simp [this, Str2Int_one]
        simp [Exp_int]
        have : 1 % m = 1 := by
          -- since m > 1
          have h := hsz_gt1
          have : 1 < m := Nat.lt_of_lt_add_one (by linarith)
          exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by linarith) (by simp [m]?))
        -- The above line is a no-op to keep tactics moving; instead reduce directly:
        simp [Exp_int]; -- Exp_int x 0 = 1
        -- 1 % m reduces to 1 because 1 < m
        have one_lt_m : 1 < m := by
          exact Nat.trans_lt (by norm_num : 0 < 1) hsz_gt1
        simp [one_lt_m]
      · -- Str2Int of base0 equals x % m
        exact hb0_val
    | cons ch t ih =>
      -- inductive step: consider processing ch after t
      have st := t.foldl f init
      have ih_all := ih
      specialize ih_all
      have ⟨r_valid, b_valid, hr_eq, hb_eq⟩ := ih_all
      let st' := (t.foldl f init)
      -- compute next state after processing ch
      -- r' = if ch='1' then (DivMod (Mul (DivMod (Mul r r).2) b).2).1 else (DivMod (Mul r r).2).1
      let prod := Mul st'.1 st'.1
      have prod_spec := Mul_spec st'.1 st'.1 r_valid r_valid
      have hprod_val := (prod_spec).2
      have hprod_valid := (prod_spec).1
      let prod_mod := (DivMod prod sz).2
      have div_prod_spec := DivMod_spec prod sz hprod_valid hz hsz_gt1
      have ⟨_, prod_mod_valid, _, prod_mod_val⟩ := div_prod_spec
      -- compute b squared mod
      have b_mul_spec := Mul_spec st'.2 st'.2 b_valid b_valid
      have hbmul_val := (b_mul_spec).2
      have hbmul_valid := (b_mul_spec).1
      let b2 := (DivMod (Mul st'.2 st'.2) sz).2
      have div_b2_spec := DivMod_spec (Mul st'.2 st'.2) sz hbmul_valid hz hsz_gt1
      have ⟨_, b2_valid, _, b2_val⟩ := div_b2_spec
      -- now handle r'
      by_cases hch : ch = '1'
      · -- when bit is '1'
        let tmp := Mul prod_mod st'.2
        -- need validity and value for tmp
        have tmp_mul_spec := Mul_spec prod_mod st'.2 prod_mod_valid b_valid
        have htmp_val := (tmp_mul_spec).2
        have htmp_valid := (tmp_mul_spec).1
        let r' := (DivMod tmp sz).2
        have div_r'_spec := DivMod_spec tmp sz htmp_valid hz hsz_gt1
        have ⟨_, r'_valid, _, r'_val⟩ := div_r'_spec
        -- Now compute numeric equalities:
        -- Str2Int r' = (Str2Int tmp) % m = (Str2Int prod_mod * Str2Int st'.2) % m
        -- Str2Int prod_mod = (Str2Int prod) % m = (Str2Int st'.1 * Str2Int st'.1) % m
        -- Use ih: Str2Int st'.1 = Exp_int x n % m, Str2Int st'.2 = Exp_int x (2^k) % m
        -- So Str2Int r' = ((Exp_int x n % m * Exp_int x n % m) % m * Exp_int x (2^k) % m) % m
        -- By modular arithmetic this equals Exp_int x (2*n + (if ch='1' then 1 else 0)) % m
        -- We perform rewrites using helper lemmas.
        have H1 : Str2Int prod = Str2Int st'.1 * Str2Int st'.1 := by exact hprod_val
        have H2 : Str2Int prod_mod = Str2Int prod % m := by exact prod_mod_val
        have H3 : Str2Int tmp = Str2Int prod_mod * Str2Int st'.2 := by exact htmp_val
        have H4 : Str2Int r
-- </vc-theorem>
end BignumLean