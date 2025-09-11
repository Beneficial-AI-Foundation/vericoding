namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

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
lemma valid_one : BignumLean.ValidBitString "1" := by
  intro i c h
  cases i with
  | zero =>
    simp at h
    injection h with hc
    subst hc
    left
    rfl
  | succ _ =>
    simp at h
    contradiction

-- LLM HELPER
lemma exp_double (x m : Nat) : BignumLean.Exp_int x (2 * m) = BignumLean.Exp_int x m * BignumLean.Exp_int x m := by
  induction m with
  | zero =>
    simp [BignumLean.Exp_int]
  | succ m ih =>
    simp [BignumLean.Exp_int]
    have : 2 * (m + 1) = (2 * m) + 2 := by
      simp [Nat.add_comm, Nat.mul_succ, Nat.mul_comm]
    rw [this]
    -- Exp_int x (2*m + 2) = x * Exp_int x (2*m + 1) = x * (x * Exp_int x (2*m)) = (x * x) * Exp_int x (2*m)
    -- Now use ih to transform Exp_int x (2*m) into Exp_int x m * Exp_int x m
    calc
      BignumLean.Exp_int x ((2 * m) + 2)
        = x * BignumLean.Exp_int x ((2 * m) + 1) := by
          simp [BignumLean.Exp_int]
      _ = x * (x * BignumLean.Exp_int x (2 * m)) := by
          simp [BignumLean.Exp_int]
      _ = (x * x) * BignumLean.Exp_int x (2 * m) := by
          ring
      _ = (x * x) * (BignumLean.Exp_int x m * BignumLean.Exp_int x m) := by
          rw [ih]
      _ = (x * BignumLean.Exp_int x m) * (x * BignumLean.Exp_int x m) := by
          ring
      _ = BignumLean.Exp_int x (m + 1) * BignumLean.Exp_int x (m + 1) := by
          simp [BignumLean.Exp_int]
-- </vc-helpers>

-- <vc-spec>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
  if hzero : Str2Int sy = 0 then
    let one : String := "1"
    (DivMod one sz).2
  else
    let r0 := (DivMod sx sz).2
    let rec loop : Nat -> String -> String
      | 0, acc => acc
      | k+1, acc =>
        let prod := Mul acc acc
        (loop k (DivMod prod sz).2)
    loop n r0
-- </vc-code>

-- <vc-theorem>
theorem ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
-- Start the proof by cases on whether sy represents 0 or a power of two.
  cases hsy_pow2 with
  | inl h_pow2 =>
    -- sy = 2^n case
    have h_nonzero : Str2Int sy ≠ 0 := by
      intro contra
      simp [contra, h_pow2] at *
      -- Exp_int 2 n = 0 impossible as Exp_int yields >=1
      have : Exp_int 2 n ≥ 1 := by
        induction n with
        | zero => simp [BignumLean.Exp_int]
        | succ n ih => simp [BignumLean.Exp_int]; apply Nat.succ_pos'
      have := Nat.pos_iff_ne_zero.1 (by linarith)
      contradiction
    -- Unfold the definition of ModExpPow2 in this branch
    dsimp [ModExpPow2]
    -- Because sy ≠ 0 the definition takes the else-branch; compute r0 and consider the loop.
    let r0 := (DivMod sx sz).2
    have dr0 := DivMod_spec sx sz hx hz (by linarith [hsz_gt1])
    have r0_valid : ValidBitString r0 := dr0.1
    have r0_eq : Str2Int r0 = Str2Int sx % Str2Int sz := dr0.3
    -- We will prove by induction on n that after k iterations we obtain x^(2^k) mod sz and validity.
    let rec aux : Nat -> String -> Prop
      | 0, acc => True
      | k+1, acc => True
    -- Formal induction on n to derive both properties for the final result.
    have : ∀ k acc, (∀ {i c}, acc.get? i = some c → (c = '0' ∨ c = '1')) → 
      (∀ m, (k = m) → 
        let res := (fun rec k' acc' => if k' = 0 then acc' else
          let prod := Mul acc' acc' in rec (k' - 1) (DivMod prod sz).2) -- dummy
        True) := by
      intro k; induction k with
      | zero =>
        intro acc hv; intro m hm; trivial
      | succ k ih =>
        intro acc hv; intro m hm; trivial
    -- Instead of proving the above dummy, perform a standard induction that mirrors the algorithm:
    induction n with
    | zero =>
      -- n = 0: The function returns r0 directly.
      dsimp [ModExpPow2]
      simp [h_pow2] at *
      -- In code, for sy nonzero we take else-branch and loop 0 r0 = r0
      have res_def : ModExpPow2 sx sy 0 sz = r0 := by
        dsimp [ModExpPow2]; simp [h_pow2]; rfl
      split
      · -- ValidBitString property from DivMod_spec
        rw [res_def]; exact r0_valid
      · -- Equality: Str2Int r0 = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz
        rw [res_def]
        -- Str2Int sy = Exp_int 2 0 = 1, so RHS is Exp_int (Str2Int sx) 1 % Str2Int sz = Str2Int sx % Str2Int sz
        have sy_eq : Str2Int sy = BignumLean.Exp_int 2 0 := by
          simp [h_pow2]
        simp [sy_eq] at *
        have : BignumLean.Exp_int (Str2Int sx) 1 = Str2Int sx := by
          simp [BignumLean.Exp_int]
        calc
          Str2Int r0 = Str2Int sx % Str2Int sz := r0_eq
          _ = BignumLean.Exp_int (Str2Int sx) 1 % Str2Int sz := by
            rw [this]
    | succ k ih =>
      -- Inductive step: assume holds for k, prove for k+1.
      dsimp [ModExpPow2] at *
      simp [h_pow2] at *
      -- Let r0 be initial remainder and define r_j after j iterations.
      let r0 := (DivMod sx sz).2
      have dr0 := DivMod_spec sx sz hx hz (by linarith [hsz_gt1])
      have r0_valid : ValidBitString r0 := dr0.1
      have r0_eq : Str2Int r0 = Str2Int sx % Str2Int sz := dr0.3
      -- Define function for iterating squares; we'll reason about its result after k steps.
      let rec loop : Nat -> String -> String
        | 0, acc => acc
        | m+1, acc => loop m (DivMod (Mul acc acc) sz).2
      -- We need to show loop (k+1) r0 yields the desired result.
      -- Use IH on k for the subproblem starting from r0 after one squaring.
      -- First, relate one-step: compute r1 = DivMod (Mul r0 r0) sz).2
      let prod0 := Mul r0 r0
      have mprod_valid := Mul_spec r0 r0 r0_valid r0_valid
      have dprod := DivMod_spec prod0 sz mprod_valid.1 hz (by linarith [hsz_gt1])
      -- dprod gives validity of (DivMod prod0 sz).2 and its integer value.
      have r1_valid : ValidBitString (DivMod prod0 sz).2 := dprod.1.2
      have r1_eq : Str2Int (DivMod prod0 sz).2 = Str2Int prod0 % Str2Int sz := dprod.2.2
      -- Use IH: we need to show that after k more iterations starting from r1 we get the desired exponentiation.
      -- By the inductive hypothesis applied to starting string r1 and exponent k:
      have ih_apply :
        (∀ (s : String), ValidBitString s →
          (let rec loop' : Nat -> String -> String
            | 0, acc => acc
            | m+1, acc => loop' m (DivMod (Mul acc acc) sz).2
           in loop' k (DivMod s sz).2) =
          (let _ := r1 in (loop k r1))) := by
        -- The equality is just to allow application of IH pattern; provide trivial proof.
        intro s hs; rfl
      -- Now apply the inductive hypothesis in the form we derived earlier:
      -- We will show Str2Int (loop (k+1) r0) = Exp_int (Str2Int sx) (Exp_int 2 (k+1)) % Str2Int sz
      have step_eq : Str2Int (loop (k+1) r0) =
        (BignumLean.Exp_int (Str2Int sx) (BignumLean.Exp_int 2 (k + 1))) % Str2Int sz := by
        -- compute loop (k+1) r0 = loop k r1 where r1 = (DivMod (Mul r0 r0) sz).2
        have : loop (k+1) r0 = loop k (DivMod (Mul r0 r0) sz).2 := rfl
        rw [this]
        -- Apply IH: for loop k starting at r1, by IH we get Str2Int (loop k r1) =
        -- Exp_int (Str2Int r1_orig) (Exp_int 2 k) % Str2Int sz where r1_orig = Str2Int r1
        -- But we need IH on k applied to starting value r1. We can perform a nested induction pattern:
        -- However, easier: use the outer inductive hypothesis (ih) on k with starting string r1.
        -- First, prove the property for k = 0 and then step; we skip formalizing nested IH by reusing the structure of ih.
        -- Instead, show algebraically:
        have r1_val : Str2Int (DivMod (Mul r0 r0) sz).2 = (Str2Int r0 * Str2Int r0) % Str2Int sz := by
          -- Mul_spec gives Str2Int prod0 = Str2Int r0 * Str2Int r0
          have mul_eq := (Mul_spec r0 r0 r0_valid r0_valid).2
          -- DivMod_spec on prod0 gives remainder equality
          have d := DivMod_spec prod0 sz (Mul_spec r0 r0 r0_valid r0_valid).1 hz (by linarith [hsz_gt1])
          exact d.2.2
        -- By the inductive hypothesis (on n), applied to k, we have:
        -- loop k r1 has integer equal to Exp_int (Str2Int r1) (Exp_int 2 k) % Str2Int sz
        -- But Str2Int r1 = (Str2Int r0 * Str2Int r0) % Str2Int sz (from r1_val).
        -- Using modular arithmetic, (a % m * a % m) % m = (a * a) % m, and exp_double lemma, we conclude.
        -- We now present the
-- </vc-proof>

end BignumLean