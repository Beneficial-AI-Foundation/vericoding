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

def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
  sorry

axiom ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz

def Zeros (n : Nat) : String :=
  sorry

axiom Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s

-- <vc-helpers>
-- LLM HELPER
def getBit (s : String) (i : Nat) : Bool :=
  match s.data[i]? with
  | some '1' => true
  | _ => false

-- LLM HELPER
def ModExpHelper (sx sy sz : String) (n : Nat) : String :=
  if n = 0 then
    if getBit sy 0 then sx else Zeros sx.length
  else
    let bit_n := if n < sy.length && getBit sy n then "1" ++ Zeros n else Zeros (n + 1)
    let partial_result := ModExpPow2 sx bit_n n sz
    let rest := ModExpHelper partial_result sy sz (n - 1)
    rest
termination_by n

-- LLM HELPER
lemma ModExpHelper_valid (sx sy sz : String) (n : Nat) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpHelper sx sy sz n) := by
  induction n generalizing sx with
  | zero =>
    simp [ModExpHelper]
    split
    · exact hx
    · exact (Zeros_spec sx.length).2.1
  | succ n' ih =>
    simp [ModExpHelper]
    let bit_n := if n' + 1 < sy.length && getBit sy (n' + 1) then "1" ++ Zeros (n' + 1) else Zeros (n' + 2)
    have bit_valid : ValidBitString bit_n := by
      unfold bit_n
      split
      · intro i c hget
        cases i with
        | zero => 
          simp [String.get?, String.data] at hget
          cases hget; left; rfl
        | succ i' =>
          have zeros_valid := (Zeros_spec (n' + 1)).2.1
          unfold ValidBitString at zeros_valid
          simp [String.get?, String.data] at hget
          exact zeros_valid hget
      · exact (Zeros_spec (n' + 2)).2.1
    have bit_pow2_or_zero : Str2Int bit_n = Exp_int 2 (n' + 1) ∨ Str2Int bit_n = 0 := by
      unfold bit_n
      split
      · left
        simp [Str2Int, String.data, List.foldl]
        have zeros_str2int := (Zeros_spec (n' + 1)).2.2.1
        simp [Str2Int] at zeros_str2int
        simp [zeros_str2int, Exp_int]
        rfl
      · right; exact (Zeros_spec (n' + 2)).2.2.1
    have bit_len : bit_n.length = n' + 2 := by
      unfold bit_n
      split
      · simp [String.length, String.data]
        have := (Zeros_spec (n' + 1)).1
        simp [this]
      · exact (Zeros_spec (n' + 2)).1
    have modexp_valid := (ModExpPow2_spec sx bit_n (n' + 1) sz hx bit_valid hz bit_pow2_or_zero bit_len hsz_gt1).1
    exact ih (ModExpPow2 sx bit_n (n' + 1) sz) modexp_valid

-- LLM HELPER
lemma ModExpHelper_spec (sx sy sz : String) (n : Nat) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz) (hsz_gt1 : Str2Int sz > 1) (hn_lt : n < sy.length) :
  Str2Int (ModExpHelper sx sy sz n) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
  induction n generalizing sx with
  | zero =>
    simp [ModExpHelper]
    split
    · simp [Exp_int]
      rfl
    · have zeros_str2int := (Zeros_spec sx.length).2.2.1
      simp [zeros_str2int, Exp_int]
      rfl
  | succ n' ih =>
    simp [ModExpHelper]
    let bit_n := if n' + 1 < sy.length && getBit sy (n' + 1) then "1" ++ Zeros (n' + 1) else Zeros (n' + 2)
    have bit_valid : ValidBitString bit_n := by
      unfold bit_n
      split
      · intro i c hget
        cases i with
        | zero => 
          simp [String.get?, String.data] at hget
          cases hget; left; rfl
        | succ i' =>
          have zeros_valid := (Zeros_spec (n' + 1)).2.1
          unfold ValidBitString at zeros_valid
          simp [String.get?, String.data] at hget
          exact zeros_valid hget
      · exact (Zeros_spec (n' + 2)).2.1
    have bit_pow2_or_zero : Str2Int bit_n = Exp_int 2 (n' + 1) ∨ Str2Int bit_n = 0 := by
      unfold bit_n
      split
      · left
        simp [Str2Int, String.data, List.foldl]
        have zeros_str2int := (Zeros_spec (n' + 1)).2.2.1
        simp [Str2Int] at zeros_str2int
        simp [zeros_str2int, Exp_int]
        rfl
      · right; exact (Zeros_spec (n' + 2)).2.2.1
    have bit_len : bit_n.length = n' + 2 := by
      unfold bit_n
      split
      · simp [String.length, String.data]
        have := (Zeros_spec (n' + 1)).1
        simp [this]
      · exact (Zeros_spec (n' + 2)).1
    have modexp_spec := (ModExpPow2_spec sx bit_n (n' + 1) sz hx bit_valid hz bit_pow2_or_zero bit_len hsz_gt1).2
    have modexp_valid := (ModExpPow2_spec sx bit_n (n' + 1) sz hx bit_valid hz bit_pow2_or_zero bit_len hsz_gt1).1
    have n'_lt : n' < sy.length := by
      cases hn_lt
      exact Nat.lt_of_succ_lt_succ hn_lt
    simp [modexp_spec]
    exact ih (ModExpPow2 sx bit_n (n' + 1) sz) modexp_valid n'_lt
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if sy.length = 0 then
    Zeros sx.length
  else
    ModExpHelper sx sy sz (sy.length - 1)
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
unfold ModExp
  split
  · simp at hsy_pos
    cases hsy_pos
  · constructor
    · have h_len : sy.length - 1 < sy.length := by
        cases sy.length with
        | zero => simp at hsy_pos; cases hsy_pos
        | succ n => simp; exact Nat.lt_succ_self n
      exact ModExpHelper_valid sx sy sz (sy.length - 1) hx hy hz hsz_gt1
    · have h_len : sy.length - 1 < sy.length := by
        cases sy.length with
        | zero => simp at hsy_pos; cases hsy_pos
        | succ n => simp; exact Nat.lt_succ_self n
      exact ModExpHelper_spec sx sy sz (sy.length - 1) hx hy hz hsz_gt1 h_len
-- </vc-proof>

end BignumLean