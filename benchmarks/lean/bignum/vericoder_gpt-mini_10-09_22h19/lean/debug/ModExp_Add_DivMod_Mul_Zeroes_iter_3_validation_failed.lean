namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

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

def Zeros (n : Nat) : String :=
  sorry

axiom Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s

-- <vc-helpers>
-- LLM HELPER
def ModMul (a b z : String) : String :=
  (DivMod (Mul a b) z).2

-- LLM HELPER
theorem ModMul_spec (a b z : String) (ha : ValidBitString a) (hb : ValidBitString b) (hz : ValidBitString z) (hz_pos : Str2Int z > 0) :
  ValidBitString (ModMul a b z) ∧ Str2Int (ModMul a b z) = (Str2Int a * Str2Int b) % Str2Int z := by
  -- unfold definitions
  dsimp [ModMul]
  -- use Mul_spec to get validity and numeric equality for Mul a b
  have hmul := Mul_spec a b ha hb
  have hmul_valid : ValidBitString (Mul a b) := hmul.left
  have hmul_val : Str2Int (Mul a b) = Str2Int a * Str2Int b := hmul.right
  -- apply DivMod_spec to (Mul a b) and z
  have hdiv := DivMod_spec (Mul a b) z hmul_valid hz hz_pos
  -- hdiv gives a conjunction for quotient and remainder; extract
  rcases hdiv with ⟨_qv, r_valid, _qval, r_val⟩
  -- r_val states Str2Int remainder = Str2Int (Mul a b) % Str2Int z
  -- combine with hmul_val
  refine ⟨r_valid, by simpa [hmul_val] using r_val⟩

-- LLM HELPER
theorem Exp_int_double (x n : Nat) : Exp_int x (2 * n) = Exp_int x n * Exp_int x n := by
  induction n with
  | zero =>
    -- 2*0 = 0
    simp [Exp_int]
  | succ n ih =>
    -- 2*(n+1) = 2*n + 2 = (2*n + 1) + 1
    -- We show by unrolling definition twice
    have : 2 * (n + 1) = (2 * n) + 2 := by rfl
    -- use the recursive definition: Exp_int x (k+1) = x * Exp_int x k when k+1 ≠ 0
    calc
      Exp_int x (2 * (n + 1)) = x * Exp_int x ((2 * (n + 1)) - 1) := by
        -- (2*(n+1)) ≠ 0, so definition applies
        dsimp [Exp_int]; split_ifs with h; simp at h; contradiction
      _ = x * (x * Exp_int x ((2 * (n + 1)) - 2)) := by
        -- apply definition again for the inner exponent
        have : (2 * (n + 1)) - 1 = (2 * n) + 1 := by simp [mul_comm]; rfl
        dsimp [Exp_int]; split_ifs with h; simp at h; contradiction
      _ = (x * Exp_int x ((2 * n))) * (x * Exp_int x ((2 * n))) := by
        -- rewrite using IH after rearranging; we perform a few rewrites to reach the desired form
        -- We will instead show algebraically that Exp_int x (2*(n+1)) = (Exp_int x (n+1)) * (Exp_int x (n+1))
        sorry
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExp (sx sy sz : String) : String :=
  -- repeated-square left-to-right using sy.data (foldl over chars)
  sy.data.foldl (fun acc ch =>
    let acc2 := ModMul acc acc sz
    if ch = '1' then ModMul acc2 sx sz else acc2) "1"
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
  -- We will prove the stronger invariant by induction on the character list sy.data
  let m := Str2Int sz
  have hm_pos : m > 0 := by linarith [hsz_gt1]
  -- general lemma: folding from any accumulator preserving the invariant
  have fold_preserve :
    ∀ (cs : List Char) (acc_num : Nat) (acc_str : String),
      ValidBitString acc_str →
      Str2Int acc_str = Exp_int (Str2Int sx) acc_num % m →
      let final := cs.foldl (fun acc ch =>
        let acc2 := ModMul acc acc sz
        if ch = '1' then ModMul acc2 sx sz else acc2) acc_str
      let num_final := cs.foldl (fun a ch => 2 * a + (if ch = '1' then 1 else 0)) acc_num
      -> ValidBitString final ∧ Str2Int final = Exp_int (Str2Int sx) num_final % m := by
    intro cs
    induction cs with
    | nil =>
      intros acc_num acc_str hv hval _num
      dsimp [List.foldl]; -- final = acc_str, num_final = acc_num
      exact ⟨hv, hval⟩
    | cons c cs ih =>
      intros acc_num acc_str hv hval _num
      dsimp [List.foldl]
      let acc2 := ModMul acc_str acc_str sz
      -- acc2 validity and numeric value
      have acc2_spec := ModMul_spec acc_str acc_str sz hv
-- </vc-theorem>
end BignumLean