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
  cases Decidable.em (sy.length = 0) with
  | inl h => 
    simp [h]
    constructor
    · exact (Zeros_spec sx.length).2.1
    · have zeros_str2int := (Zeros_spec sx.length).2.2.1
      simp [zeros_str2int]
      have sy_empty : sy.data = [] := by
        cases sy with | mk data => simp [String.length] at h; cases data; rfl; simp at h
      simp [Str2Int, sy_empty, List.foldl, Exp_int]
      simp [Nat.zero_mod]
  | inr h =>
    simp [h]
    constructor
    · induction sy.length - 1 generalizing sx with
      | zero =>
        simp [ModExpHelper]
        cases Decidable.em (getBit sy 0) with
        | inl _ => simp [*]; exact hx
        | inr _ => simp [*]; exact (Zeros_spec sx.length).2.1
      | succ n' ih =>
        simp [ModExpHelper]
        let bit_n := if n' + 1 < sy.length && getBit sy (n' + 1) then "1" ++ Zeros (n' + 1) else Zeros (n' + 2)
        have bit_valid : ValidBitString bit_n := by
          unfold bit_n
          cases Decidable.em (n' + 1 < sy.length && getBit sy (n' + 1)) with
          | inl _ =>
            simp [*]
            intro i c hget
            cases i with
            | zero => 
              simp [String.get?, String.data] at hget
              cases hget; left; rfl
            | succ i' =>
              have zeros_valid := (Zeros_spec (n' + 1)).2.1
              unfold ValidBitString at zeros_valid
              simp [String.get?, String.data] at hget
              exact zeros_valid hget
          | inr _ =>
            simp [*]
            exact (Zeros_spec (n' + 2)).2.1
        have bit_pow2_or_zero : Str2Int bit_n = Exp_int 2 (n' + 1) ∨ Str2Int bit_n = 0 := by
          unfold bit_n
          cases Decidable.em (n' + 1 < sy.length && getBit sy (n' + 1)) with
          | inl _ =>
            simp [*]
            left
            simp [Str2Int, String.data, List.foldl]
            have zeros_str2int := (Zeros_spec (n' + 1)).2.2.1
            simp [Str2Int] at zeros_str2int
            simp [zeros_str2int]
            induction n' with
            | zero => simp [Exp_int]
            | succ n'' ih' => simp [Exp_int]; ring_nf; simp [ih']
          | inr _ =>
            simp [*]
            right
            exact (Zeros_spec (n' + 2)).2.2.1
        have bit_len : bit_n.length = n' + 2 := by
          unfold bit_n
          cases Decidable.em (n' + 1 < sy.length && getBit sy (n' + 1)) with
          | inl _ =>
            simp [*, String.length, String.data]
            have := (Zeros_spec (n' + 1)).1
            simp [this]
          | inr _ =>
            simp [*]
            exact (Zeros_spec (n' + 2)).1
        have modexp_valid := (ModExpPow2_spec sx bit_n (n' + 1) sz hx bit_valid hz bit_pow2_or_zero bit_len hsz_gt1).1
        exact ih (ModExpPow2 sx bit_n (n' + 1) sz) modexp_valid
    · have h_len : sy.length - 1 < sy.length := by
        cases sy.length with
        | zero => contradiction
        | succ n => simp; exact Nat.lt_succ_self n
      induction sy.length - 1 generalizing sx with
      | zero =>
        simp [ModExpHelper]
        cases Decidable.em (getBit sy 0) with
        | inl hbit =>
          simp [hbit]
          have sy_one : Str2Int sy = 1 := by
            have : sy.length = 1 := by
              cases sy.length with
              | zero => contradiction
              | succ n => simp at *; exact Nat.eq_of_sub_eq_zero ‹n - 0 = 0›
            simp [Str2Int, getBit] at hbit
            cases sy with | mk data =>
              simp [String.length] at this
              cases data with
              | nil => simp at this
              | cons c cs =>
                simp at this
                cases cs with
                | nil =>
                  simp [Str2Int, List.foldl]
                  simp [String.data] at hbit
                  cases c <;> simp at hbit <;> simp
                | cons _ _ => simp at this
          simp [sy_one, Exp_int]
        | inr hbit =>
          simp [hbit]
          have zeros_str2int := (Zeros_spec sx.length).2.2.1
          simp [zeros_str2int]
          have sy_zero : Str2Int sy = 0 := by
            have : sy.length = 1 := by
              cases sy.length with
              | zero => contradiction
              | succ n => simp at *; exact Nat.eq_of_sub_eq_zero ‹n - 0 = 0›
            simp [Str2Int, getBit] at hbit
            cases sy with | mk data =>
              simp [String.length] at this
              cases data with
              | nil => simp at this
              | cons c cs =>
                simp at this
                cases cs with
                | nil =>
                  simp [Str2Int, List.foldl]
                  simp [String.data] at hbit
                  cases c <;> simp at hbit <;> simp
                | cons _ _ => simp at this
          simp [sy_zero, Exp_int, Nat.zero_mod]
      | succ n' ih =>
        simp [ModExpHelper]
        apply ih
        let bit_n := if n' + 1 < sy.length && getBit sy (n' + 1) then "1" ++ Zeros (n' + 1) else Zeros (n' + 2)
        have bit_valid : ValidBitString bit_n := by
          unfold bit_n
          cases Decidable.em (n' + 1 < sy.length && getBit sy (n' + 1)) with
          | inl _ =>
            simp [*]
            intro i c hget
            cases i with
            | zero => 
              simp [String.get?, String.data] at hget
              cases hget; left; rfl
            | succ i' =>
              have zeros_valid := (Zeros_spec (n' + 1)).2.1
              unfold ValidBitString at zeros_valid
              simp [String.get?, String.data] at hget
              exact zeros_valid hget
          | inr _ =>
            simp [*]
            exact (Zeros_spec (n' + 2)).2.1
        have bit_pow2_or_zero : Str2Int bit_n = Exp_int 2 (n' + 1) ∨ Str2Int bit_n = 0 := by
          unfold bit_n
          cases Decidable.em (n' + 1 < sy.length && getBit sy (n' + 1)) with
          | inl _ =>
            simp [*]
            left
            simp [Str2Int, String.data, List.foldl]
            have zeros_str2int := (Zeros_spec (n' + 1)).2.2.1
            simp [Str2Int] at zeros_str2int
            simp [zeros_str2int]
            induction n' with
            | zero => simp [Exp_int]
            | succ n'' ih' => simp [Exp_int]; ring_nf; simp [ih']
          | inr _ =>
            simp [*]
            right
            exact (Zeros_spec (n' + 2)).2.2.1
        have bit_len : bit_n.length = n' + 2 := by
          unfold bit_n
          cases Decidable.em (n' + 1 < sy.length && getBit sy (n' + 1)) with
          | inl _ =>
            simp [*, String.length, String.data]
            have := (Zeros_spec (n' + 1)).1
            simp [this]
          | inr _ =>
            simp [*]
            exact (Zeros_spec (n' + 2)).1
        exact (ModExpPow2_spec sx bit_n (n' + 1) sz hx bit_valid hz bit_pow2_or_zero bit_len hsz_gt1).1
-- </vc-proof>

end BignumLean