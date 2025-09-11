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
    calc
      Exp_int x (a + b + 1) = x * Exp_int x (a + b) := by simp [Exp_int]
      _ = x * (Exp_int x a * Exp_int x b) := by rw [ih]
      _ = (Exp_int x a) * (x * Exp_int x b) := by
        rw [mul_comm (Exp_int x a) (x * Exp_int x b)]
        rfl

-- LLM HELPER
theorem Exp_int_two_mul (x n : Nat) : Exp_int x (2 * n) = Exp_int x n * Exp_int x n := by
  calc
    Exp_int x (2 * n) = Exp_int x (n + n) := by
      simp [Nat.mul_comm]
    _ = Exp_int x n * Exp_int x n := by
      rw [Exp_int_add x n n]

-- LLM HELPER
theorem mod_mul_mod (a b m : Nat) : (a * b) % m = ((a % m) * (b % m)) % m := by
  calc
    (a * b) % m = ((a % m) * b) % m := by apply Nat.mul_mod
    _ = ((a % m) * ((b % m) + m * (b / m))) % m := by
      have := Nat.mod_add_div b m
      rw [this]
    _ = (((a % m) * (b % m) + (a % m) * m * (b / m))) % m := by
      rw [mul_add, mul_assoc]
    _ = ((a % m) * (b % m)) % m := by
      -- terms with a factor m vanish modulo m
      -- use the fact (u + v * m) % m = u % m
      have : (((a % m) * (b % m) + (a % m) * m * (b / m))) % m = ((a % m) * (b % m)) % m := by
        apply Nat.add_mul_mod_left
      exact this

-- LLM HELPER
theorem Str2Int_one : Str2Int "1" = 1 := by
  -- "1".data = ['1']
  show "1".data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = 1
  -- compute directly
  simp [String.data]
  -- foldl over single element yields 2*0 + 1 = 1
  rfl
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
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz
-- </vc-theorem>
-- <vc-proof>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
  set x := Str2Int sx
  set m := Str2Int sz
  -- base0 := sx % sz information
  have div0 := DivMod_spec sx sz hx hz (by linarith : Str2Int sz > 0)
  have ⟨_q0_valid, base0_valid, _q0_val, base0_val⟩ := div0
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
  let l := sy.data

  -- helper: value of a prefix as Nat
  let val_of := fun (t : List Char) => t.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

  -- Invariant: after folding t we have desired properties
  have IH : ∀ (t : List Char),
    let st := t.foldl f init in
    ValidBitString st.1 ∧ ValidBitString st.2 ∧
    Str2Int st.1 = Exp_int x (val_of t) % m ∧
    Str2Int st.2 = Exp_int x (2 ^ t.length) % m := by
    intro t
    induction t with
    | nil =>
      simp [init]
      -- ValidBitString "1"
      constructor
      · intro i c hc
        cases i with
        | zero =>
          simp at hc
          injection hc with h
          subst h
          left; rfl
        | succ _ =>
          simp at hc
          contradiction
      -- ValidBitString base0
      constructor
      · exact base0_valid
      constructor
      -- Str2Int "1" = Exp_int x (val_of []) % m
      ·
        have val_nil : val_of ([] : List Char) = 0 := by simp [val_of]; rfl
        simp [val_nil, Str2Int_one, Exp_int]
        have one_lt_m : 1 < m := by
          exact hsz_gt1
        -- 1 % m = 1 because 1 < m
        exact (congrArg (fun a => a % m) (by rfl) : _ ) -- trivial step to proceed
      -- Str2Int base0 = Exp_int x (2 ^ 0) % m
      ·
        -- Exp_int x (2 ^ 0) = Exp_int x 1 = x
        have pow0 : 2 ^ 0 = 1 := by norm_num
        have exp1 : Exp_int x 1 = x := by simp [Exp_int]
        simp [pow0, exp1]
        -- base0_val: Str2Int base0 = x % m
        exact base0_val
    | cons ch t ih =>
      let st := t.foldl f init
      have ih_all := ih
      -- unpack IH for t
      have ⟨r_valid, b_valid, hr_eq, hb_eq⟩ := ih_all
      -- compute prod = Mul r r
      let prod := Mul st.1 st.1
      have prod_spec := Mul_spec st.1 st.1 r_valid r_valid
      have prod_valid := prod_spec.1
      have prod_val := prod_spec.2
      -- prod_mod = (DivMod prod sz).2
      let prod_mod := (DivMod prod sz).2
      have div_prod := DivMod_spec prod sz prod_valid hz (by linarith : Str2Int sz > 0)
      have ⟨_ , prod_mod_valid, _ , prod_mod_val⟩ := div_prod
      -- b squared mod
      let bmul := Mul st.2 st.2
      have bmul_spec := Mul_spec st.2 st.2 b_valid b_valid
      have bmul_val := bmul_spec.2
      have bmul_valid := bmul_spec.1
      let b2 := (DivMod bmul sz).2
      have div_b2 := DivMod_spec bmul sz bmul_valid hz (by linarith : Str2Int sz > 0)
      have ⟨_, b2_valid, _, b2_val⟩ := div_b2

      -- prove new invariants depending on ch
      by_cases hch : ch = '1'
      · -- ch = '1'
        -- tmp = Mul prod_mod st.2
        let tmp := Mul prod_mod st.2
        have tmp_spec := Mul_spec prod_mod st.2 prod_mod_valid b_valid
        have tmp_valid := tmp_spec.1
        have tmp_val := tmp_spec.2
        let r' := (DivMod tmp sz).2
        have div_r' := DivMod_spec tmp sz tmp_valid hz (by linarith : Str2Int sz > 0)
        have ⟨_, r'_valid, _, r'_val⟩ := div_r'
        -- Now establish numeric equalities
        -- Str2Int prod = Str2Int st.1 * Str2Int st.1
        have Hprod : Str2Int prod = Str2Int st.1 * Str2Int st.1 := prod_val
        -- Str2Int prod_mod = Str2Int prod % m
        have Hprod_mod : Str2Int prod_mod = Str2Int prod % m := prod_mod_val
        -- Str2Int tmp = Str2Int prod_mod * Str2Int st.2
        have Htmp : Str2Int tmp = Str2Int prod_mod * Str2Int st.2 := tmp_val
        -- Now substitute IH equalities
        have A : Str2Int st.1 = Exp_int x (val_of t) % m := hr_eq
        have B : Str2Int st.2 = Exp_int x (2 ^ t.length) % m := hb_eq
        -- compute Str2Int r'
        have step1 : Str2Int r' = (Str2Int prod_mod * Str2Int st.2) % m := by
          calc
            Str2Int r' = Str2Int tmp % m := by exact r'_val
            _ = (Str2Int prod_mod * Str2Int st.2) % m := by rw [Htmp]
        -- rewrite prod_mod using Hprod_mod and Hprod and A
        have prod_eq : Str2Int prod_mod = (Exp_int x (val_of t) * Exp_int x (val_of t)) % m := by
          calc
            Str2Int prod_mod = Str2Int prod % m := by exact Hprod_mod
            _ = (Str2Int st.1 * Str2Int st.1) % m := by rw [Hprod]
            _ = ((Exp_int x (val_of t) % m) * (Exp_int x (val_of t) % m))
-- </vc-proof>

end BignumLean