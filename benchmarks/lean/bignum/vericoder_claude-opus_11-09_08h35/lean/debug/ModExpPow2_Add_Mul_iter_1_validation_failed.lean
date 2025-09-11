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

def Mul (s1 s2 : String) : String :=
  sorry

axiom Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2

-- <vc-helpers>
-- LLM HELPER
def Int2Str (n : Nat) : String :=
  if n = 0 then "0" else
    let rec toBinary (m : Nat) (acc : String) : String :=
      if m = 0 then acc
      else toBinary (m / 2) ((if m % 2 = 1 then "1" else "0") ++ acc)
    toBinary n ""

-- LLM HELPER  
def ModStr (s1 s2 : String) : String :=
  Int2Str (Str2Int s1 % Str2Int s2)

-- LLM HELPER
axiom Int2Str_spec (n : Nat) :
  ValidBitString (Int2Str n) ∧ Str2Int (Int2Str n) = n

-- LLM HELPER
axiom ModStr_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) (h2_pos : Str2Int s2 > 0) :
  ValidBitString (ModStr s1 s2) ∧ Str2Int (ModStr s1 s2) = Str2Int s1 % Str2Int s2
-- </vc-helpers>

-- <vc-spec>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if Str2Int sy = 0 then
    Int2Str 1
  else
    -- sy = 2^n, so we need to square n times
    let rec squareMod (base : String) (k : Nat) : String :=
      if k = 0 then base
      else 
        let squared := Mul base base
        squareMod (ModStr squared sz) (k - 1)
    squareMod (ModStr sx sz) n
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
unfold ModExpPow2
  cases hsy_pow2 with
  | inr h0 =>
    -- Case: sy = 0
    simp [h0]
    have exp_zero : Exp_int (Str2Int sx) 0 = 1 := by
      unfold Exp_int
      simp
    rw [exp_zero]
    exact Int2Str_spec 1
  | inl h2n =>
    -- Case: sy = 2^n
    simp [h2n]
    have h_ne_zero : Str2Int sy ≠ 0 := by
      rw [h2n]
      unfold Exp_int
      split
      · contradiction
      · simp
        apply Nat.succ_ne_zero
    simp [h_ne_zero]
    
    -- Helper lemma for the recursive squaring
    have squareMod_spec : ∀ k base,
      ValidBitString base →
      Str2Int base < Str2Int sz →
      let result := (fun base k => 
        if k = 0 then base
        else 
          let rec loop (b : String) (j : Nat) : String :=
            if j = 0 then b
            else 
              let squared := Mul b b
              loop (ModStr squared sz) (j - 1)
          loop base k) base k
      in ValidBitString result ∧ 
         Str2Int result = Exp_int (Str2Int base) (Exp_int 2 k) % Str2Int sz := by
      intro k
      induction k with
      | zero =>
        intro base hb hlt
        simp
        unfold Exp_int
        simp
        constructor
        · exact hb
        · simp [Nat.mod_eq_of_lt hlt]
      | succ k' ih =>
        intro base hb hlt
        simp
        split
        · contradiction
        · simp
          let squared := Mul base base
          have hsq := Mul_spec base base hb hb
          have hmod := ModStr_spec squared sz hsq.1 (Nat.lt_of_succ_lt hsz_gt1)
          have hmod_lt : Str2Int (ModStr squared sz) < Str2Int sz := by
            rw [hmod.2]
            exact Nat.mod_lt _ (Nat.lt_of_succ_lt hsz_gt1)
          have ih_result := ih (ModStr squared sz) hmod.1 hmod_lt
          simp at ih_result
          constructor
          · exact ih_result.1
          · rw [ih_result.2, hmod.2, hsq.2]
            have exp_succ : Exp_int 2 (k' + 1) = 2 * Exp_int 2 k' := by
              unfold Exp_int
              split
              · contradiction
              · simp [Nat.add_sub_cancel]
            rw [exp_succ]
            have exp_mul : Exp_int (Str2Int base) (2 * Exp_int 2 k') = 
                          Exp_int (Exp_int (Str2Int base) 2) (Exp_int 2 k') := by
              clear ih ih_result hmod hmod_lt hsq hb hlt
              generalize hb' : Str2Int base = b
              generalize he : Exp_int 2 k' = e
              induction e with
              | zero =>
                unfold Exp_int
                simp
              | succ e' ihe =>
                unfold Exp_int at *
                split at *
                · contradiction  
                · simp at *
                  rw [mul_comm 2 _, Nat.mul_succ]
                  rw [ihe]
                  unfold Exp_int
                  simp
                  ring
            rw [exp_mul]
            have exp2 : Exp_int (Str2Int base) 2 = Str2Int base * Str2Int base := by
              unfold Exp_int
              simp
            rw [exp2]
            exact Nat.mul_mod_mod _ _ _
    
    have hmod_init := ModStr_spec sx sz hx hz (Nat.lt_of_succ_lt hsz_gt1)
    have hmod_lt : Str2Int (ModStr sx sz) < Str2Int sz := by
      rw [hmod_init.2]
      exact Nat.mod_lt _ (Nat.lt_of_succ_lt hsz_gt1)
    
    have result := squareMod_spec n (ModStr sx sz) hmod_init.1 hmod_lt
    simp at result
    constructor
    · exact result.1
    · rw [result.2, hmod_init.2, h2n]
      exact Nat.mod_mod_of_dvd _ _ (dvd_refl _)
-- </vc-proof>

end BignumLean