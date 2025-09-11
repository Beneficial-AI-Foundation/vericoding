namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

def DivMod (dividend divisor : String) : (String × String) :=
  sorry

axiom DivMod_spec (dividend divisor : String) (h1 : ValidBitString dividend) (h2 : ValidBitString divisor) (h_pos : Str2Int divisor > 0) :
  let (quotient, remainder) := DivMod dividend divisor
  ValidBitString quotient ∧ ValidBitString remainder ∧
  Str2Int quotient = Str2Int dividend / Str2Int divisor ∧
  Str2Int remainder = Str2Int dividend % Str2Int divisor

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
theorem Exp_int_succ (x n : Nat) : Exp_int x (n + 1) = x * Exp_int x n := by
  have hne : (n + 1) ≠ 0 := Nat.succ_ne_zero n
  dsimp [Exp_int]
  simp [if_neg hne]
  -- (n+1) - 1 = n
  have : (n + 1) - 1 = n := by simp
  rw [this]
  rfl

-- LLM HELPER
theorem Exp_int_add (x a : Nat) : ∀ b, Exp_int x (a + b) = Exp_int x a * Exp_int x b := by
  intro b
  induction b with
  | zero =>
    -- a + 0 = a, and Exp_int x 0 = 1
    have E0 : Exp_int x 0 = 1 := by dsimp [Exp_int]; simp
    calc
      Exp_int x (a + 0) = Exp_int x a := by rw [Nat.add_zero]
      _ = Exp_int x a * 1 := by simp
      _ = Exp_int x a * Exp_int x 0 := by rw [E0]
  | succ b ih =>
    -- a + succ b = succ (a + b)
    calc
      Exp_int x (a + succ b) = Exp_int x (succ (a + b)) := by rw [by simp (config := {singlePass := true}) : a + succ b = succ (a + b)]
      _ = x * Exp_int x (a + b) := by apply Exp_int_succ
      _ = x * (Exp_int x a * Exp_int x b) := by rw [ih]
      _ = Exp_int x a * (x * Exp_int x b) := by simp [mul_assoc]
      _ = Exp_int x a * Exp_int x (succ b) := by rw [Exp_int_succ x b]

-- LLM HELPER
theorem Exp_int_two_mul (x e : Nat) : Exp_int x (2 * e) = Exp_int x e * Exp_int x e := by
  -- 2 * e = e + e
  have : 2 * e = e + e := by
    simp [Nat.add_comm]
  rw [this]
  exact Exp_int_add x e e

-- LLM HELPER
def ModMul (a b m : String) : String := (DivMod (Mul a b) m).2

-- LLM HELPER
theorem ModMul_spec (a b m : String) (ha : ValidBitString a) (hb : ValidBitString b) (hm : ValidBitString m) (hpos : Str2Int m > 0) :
  ValidBitString (ModMul a b m) ∧ Str2Int (ModMul a b m) = (Str2Int a * Str2Int b) % Str2Int m := by
  let prod := Mul a b
  let mult_spec := Mul_spec a b ha hb
  let hprod_valid := mult_spec.left
  let hprod_eq := mult_spec.right
  -- apply DivMod_spec to prod and m
  have dspec := DivMod_spec prod m hprod_valid hm hpos
  -- destruct nested conjunctions
  match dspec with
  | And.intro q_valid rest =>
    match rest with
    | And.intro r_valid rest2 =>
      match rest2 with
      | And.intro q_eq r_eq =>
        constructor
        · -- validity of remainder
          exact r_valid
        · -- numeric equality: rewrite remainder equality then product equality
          calc
            Str2Int (ModMul a b m) = Str2Int ((DivMod prod m).2) := rfl
            _ = Str2Int ((DivMod prod m).2) := rfl
            _ = Str2Int ((DivMod prod m).2) := rfl
            _ = Str2Int ((DivMod prod m).2) := by rfl
            _ = Str2Int prod % Str2Int m := by rw [r_eq]
            _ = (Str2Int a * Str2Int b) % Str2Int m := by rw [hprod_eq]

-- LLM HELPER
theorem ValidBitString_one : ValidBitString "1" := by
  intros i c h
  cases i with
  | zero =>
    have : "1".get? 0 = some '1' := by simp
    rw [this] at h
    injection h with hc
    subst hc
    right; rfl
  | succ k =>
    have : "1".get? (k + 1) = none := by simp
    rw [this] at h
    cases h

-- LLM HELPER
theorem Str2Int_one : Str2Int "1" = 1 := by
  dsimp [Str2Int]
  simp

-- LLM HELPER
theorem foldl_expfold_eq_Str2Int (s : String) :
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = Str2Int s := by
  dsimp [Str2Int]; rfl
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExp (sx sy sz : String) : String :=
  let step := fun (acc : String) (ch : Char) =>
    let acc2 := ModMul acc acc sz
    if ch = '1' then ModMul acc2 sx sz else acc2
  sy.data.foldl step "1"
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz
-- </vc-theorem>
-- <vc-proof>
by
  let m := Str2Int sz
  have hmpos : m > 0 := by linarith
  let step := fun (acc : String) (ch : Char) =>
    let acc2 := ModMul acc acc sz
    if ch = '1' then ModMul acc2 sx sz else acc2
  let expfold := fun (accv : Nat) (ch : Char) => 2 * accv + (if ch = '1' then 1 else 0)
  -- general induction over the list of chars
  have IH_general :
    ∀ (l : List Char) (acc : String) (acc_val : Nat),
      ValidBitString acc →
      Str2Int acc = Exp_int (Str2Int sx) acc_val % m →
      ValidBitString (l.foldl step acc) ∧
      Str2Int (l.foldl step acc) = Exp_int (Str2Int sx) (l.foldl expfold acc_val) % m := by
    intro l
    induction l generalizing acc acc_val with
    | nil =>
      intros acc acc_val Hvalid Heq
      simp [List.foldl]
      exact ⟨Hvalid, Heq⟩
    | cons hd tl ih =>
      intros acc acc_val Hvalid Heq
      -- compute acc2 = ModMul acc acc sz
      have acc2_spec := ModMul_spec acc acc sz Hvalid Hvalid hz hmpos
      have Hacc2_valid := acc2_spec.left
      have Hacc2_eq := acc2_spec.right
      by_cases h1 : hd = '1'
      · -- hd = '1' branch
        have acc'_spec := ModMul_spec (ModMul acc acc sz) sx sz Hacc2_valid hx hz hmpos
        have Hacc'_valid := acc'_spec.left
        have Hacc'_eq := acc'_spec.right
        let new_acc_val := expfold acc_val hd
        -- compute numeric value of new accumulator
        calc
          Str2Int (if hd = '1' then ModMul (ModMul acc acc sz) sx sz else ModMul acc acc sz)
              = Str2Int (ModMul (ModMul acc acc sz) sx sz) := by simp [h1]
          _ = (Str2Int (ModMul acc acc sz) * Str2Int sx) % m := by rw [Hacc'_eq]
          _ = ((Str2Int acc * Str2Int acc) % m * Str2Int sx) % m := by rw [Hacc2_eq]
          _ = (Str2Int acc * Str2Int acc * Str2Int sx) % m := by
            -- use Nat.mul_mod: (u * v) % m = ((u % m) * v) % m
            let u := Str2Int acc * Str2Int acc
            have hmul := Nat.mul_mod u (Str2Int sx) m
            rw [←hmul]
            rfl
          _ = (Exp_int (Str2Int sx) acc_val * Exp_int (Str2Int sx) acc_val * Str2Int sx) % m := by
            -- replace Str2Int acc by its residue Exp_int ... % m twice, then remove the % using mul_mod repeatedly
            have Hacc_mod := Heq
            -- rewrite Str2Int acc as (Exp_int ... % m)
            rw [Hacc_mod] at *
            -- now use mul_mod to remove the % from the combined product
            let A := (Exp_int (Str2Int sx) acc_val) * (Exp_int (Str2Int sx) acc_val) * Str2Int sx
            have use1 := Nat.mul_mod ((Exp_int (Str2Int sx) acc_val) * (Exp_int (Str2Int sx) acc_val)) (Str2Int sx) m
            rw [←use1]
            rfl
          _ = Exp_int (Str2Int sx) (2 * acc_val + 1) % m := by
            -- show Exp_int (2*acc_val+1) = Exp_int acc_val * Exp_int acc_val * Str2Int sx
            calc
              Exp_int (Str2Int sx) (2 * acc_val + 1)
                  = Exp_int (Str2Int sx) (acc_val + acc_val + 1) := by rfl
              _ = (Exp_int (Str2Int sx) (acc_val + acc_val)) * Exp_int (Str2Int sx) 1 := by
                rw [Exp_int_succ (Str2Int sx) (acc_val + acc_val)]
              _ = (Exp_int (Str2Int sx) acc_val * Exp_int (Str2Int sx) acc_val) * Str2Int (Str2Int sx) := by
                -- use Exp_int_add and Exp_int_succ( ... ) for Exp_int 1 = 1
                have Eadd := Exp_int_add (Str2Int sx) acc_val acc_val
                rw [Eadd]
                dsimp [Exp_int]
                -- Exp_int (Str2Int sx) 1 = Str2Int sx
                have E1 : Exp_int (Str2Int sx) 1 = Str2Int sx := by
                  dsimp [Exp_int]; simp
                rw [E1]
              -- now take mod m
              rfl
        -- now we have both valid and numeric equalities for the new accumulator; continue with tail
        have := ih (ModMul (ModMul acc acc sz) sx sz) new_acc_val Hacc'_valid (by
          -- assemble equality Str2Int new_acc = Exp_int ... % m; we established it in the calc above, but need exact expression
          simp [h1] at *
          -- the last line of calc produced the needed equality; we can extract it by exactness of the goal shape
          — this is a seam to satisfy Lean's flow)
        -- The above style of extracting is awkward; instead re-produce the two facts and call ih
        have new_valid : ValidBitString (ModMul (ModMul acc acc sz) sx sz) := Hacc'_valid
        have new_eq : Str2Int (ModMul (ModMul acc acc sz) sx sz) = Exp_int (Str2Int sx) new_acc_val % m := by
          -- replicate the previous calc but produce a single equality
          simp [h1]
          rw [Hacc'_eq, Hacc2_eq, Heq]
          -- remove intermediate mods: ((a % m) * (a % m) * b) % m = (a * a * b) % m
          let u := Exp_int (Str2Int sx) acc_val
          have use1 := Nat.mul_mod (u * u) (Str2Int sx) m
          rw [←use1]
          rfl
        -- apply IH on tail
        have rest := ih _ _ new_valid new_eq
        exact rest
      · -- hd ≠ '1' branch
        have Hacc'_valid := Hacc2_valid
        have Hacc'_eq := Hacc2_eq
        let new_acc_val := expfold acc_val hd
        -- compute numeric value for the unchanged acc2
        have new_eq : Str2Int (if hd = '1' then ModMul (ModMul acc acc sz) sx sz else ModMul acc acc sz) =
                      Exp_int (Str2Int sx) new_acc_val % m := by
          simp [h1]
          -- Str2Int (ModMul acc acc sz) = (Str2Int acc * Str2Int acc) % m
          rw [Hacc2_eq]
          -- replace Str2Int acc by Exp_int ... % m
          rw [Heq]
          -- combine mods
          let u := Exp_int (Str2Int sx) acc_val
          have use1 := Nat.mul_mod (u * u) 1 m
          -- we don't need the last rewrite; instead observe:
          calc
            ((Exp_int (Str2Int sx) acc_val % m) * (Exp_int (Str2Int sx) acc_val % m)) % m
                = (Exp_int (Str2Int sx) acc_val * Exp_int (Str2Int sx) acc_val) % m := by
              let uu := Exp_int (Str2Int sx) acc_val
              have mm := Nat.mul_mod uu (Exp_int (Str2Int sx) acc_val) m
              rw [←mm]
              rfl
            _ = Exp_int (Str2Int sx) (2 * acc_val) % m := by
              have Eadd := Exp_int_two_mul (Str2Int sx) acc_val
              rw [Eadd]
        -- apply IH to tail
        have new_valid := Hacc'_valid
        have rest := ih _ _ new_valid new_eq
        exact rest
  -- apply IH_general to the full sy.data with initial acc "1" and acc_val 0
  have init_valid : ValidBitString "1" := ValidBitString_one
  have init_eq : Str2Int "1" = Exp_int (Str2Int sx) 0 % m := by
    -- Str2Int "1" = 1 and Exp_int ... 0 = 1, and 1 % m = 1 because m > 1
    calc
      Str2Int "1" = 1 := by apply Str2Int_one
      _ = Exp_int (Str2Int sx) 0 := by dsimp [Exp_int]; simp
      _ = Exp_int (Str2Int sx) 0 % m := by
        have : 1 < m := by linarith
        rw [Nat.mod_eq_of_lt this]
  have final := IH_general sy.data "1" 0 init_valid init_eq
  -- finish: show ValidBitString and numeric equality, rewrite Str2Int sy definition
  have val := (final).left
  have num := (final).right
  constructor
  · exact val
  · -- Str2Int sy = sy.data.foldl expfold 0 by definition
    have H := foldl_expfold_eq_Str2Int sy
    rw [←H] at num
    exact num
-- </vc-proof>

end BignumLean