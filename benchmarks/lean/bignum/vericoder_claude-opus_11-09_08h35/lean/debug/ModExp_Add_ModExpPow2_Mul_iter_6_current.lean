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

-- <vc-helpers>
-- LLM HELPER
def isZero (s : String) : Bool :=
  s.all (· = '0') || s.isEmpty

-- LLM HELPER
def isOne (s : String) : Bool :=
  s = "1" || (s.length > 0 && s.get (s.length - 1) = '1' && s.take (s.length - 1) |>.all (· = '0'))

-- LLM HELPER
def shiftRight (s : String) : String :=
  if s.length ≤ 1 then "0" else s.take (s.length - 1)

-- LLM HELPER
def lastBit (s : String) : Char :=
  if s.length > 0 then s.get (s.length - 1) else '0'

-- LLM HELPER
def toString (n : Nat) : String :=
  if n = 0 then "0"
  else if n = 1 then "1"
  else toString (n / 2) ++ (if n % 2 = 0 then "0" else "1")
termination_by n

-- LLM HELPER
def sub (a b : String) : String :=
  let na := Str2Int a
  let nb := Str2Int b
  if na ≥ nb then toString (na - nb) else "0"

-- LLM HELPER
def modReduce (x m : String) : String :=
  let nx := Str2Int x
  let nm := Str2Int m
  if nm = 0 then x
  else toString (nx % nm)

-- LLM HELPER
def modMul (a b m : String) : String :=
  let prod := Mul a b
  modReduce prod m

-- LLM HELPER
lemma shiftRight_length_decreases (s : String) (h : s.length > 1) :
  (shiftRight s).length < s.length := by
  unfold shiftRight
  split_ifs with h'
  · simp
    omega
  · simp [String.length_take]
    omega

-- LLM HELPER
lemma isZero_false_length (s : String) (h : ¬isZero s = true) :
  s.length > 0 := by
  unfold isZero at h
  by_contra h'
  simp at h'
  simp [h', String.isEmpty] at h

-- LLM HELPER
lemma isOne_false_of_not_zero (s : String) (h1 : ¬isZero s = true) (h2 : ¬isOne s = true) :
  s.length > 1 := by
  unfold isZero isOne at *
  by_contra h'
  push_neg at h'
  interval_cases s.length
  · simp [String.isEmpty] at h1
  · have : s.data.length = 1 := by simp [←String.length]
    match hs : s.data with
    | [] => simp at this
    | [c] => 
      simp at h2
      apply h2
      right
      constructor
      · exact this
      constructor
      · simp [String.get, hs]; rfl
      · simp [String.take, hs]
    | _::_::_ => simp at this
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if isZero sy then
    "1"  -- x^0 = 1
  else if isOne sy then
    modReduce sx sz  -- x^1 = x mod z
  else
    -- Use square-and-multiply algorithm
    let bit := lastBit sy
    let sy' := shiftRight sy
    let recResult := ModExp sx sy' sz
    let squared := modMul recResult recResult sz
    if bit = '1' then
      modMul squared sx sz
    else
      squared
termination_by sy.length
decreasing_by
  apply shiftRight_length_decreases
  apply isOne_false_of_not_zero <;> assumption
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
generalize hlen : sy.length = n
induction n using Nat.strong_induction_on generalizing sx sy sz with
| _ n ih =>
  subst hlen
  unfold ModExp
  split_ifs with h1 h2
  · -- Case: sy is zero
    constructor
    · intro i c hc
      simp at hc
      cases hc
      right
      rfl
    · have sy_zero : Str2Int sy = 0 := by
        unfold isZero Str2Int at h1
        cases h1 with
        | inl hall =>
          clear ih
          induction sy.data with
          | nil => simp
          | cons hd tl ih2 =>
            simp [List.foldl]
            have : hd = '0' := hall hd (List.mem_cons_self _ _)
            simp [this]
            exact ih2 (fun c hc => hall c (List.mem_cons_of_mem _ hc))
        | inr hemp =>
          simp [String.isEmpty] at hemp
          simp [hemp, Str2Int]
      simp [sy_zero, Exp_int]
      exact Nat.mod_eq_of_lt hsz_gt1
  · -- Case: sy is one  
    have sy_one : Str2Int sy = 1 := by
      unfold isOne at h2
      cases h2 with
      | inl heq =>
        simp [heq, Str2Int]
      | inr hpad =>
        simp [Str2Int]
        have : sy.data.length > 0 := by simp [←String.length]; exact hpad.1
        match hd : sy.data with
        | [] => simp at this
        | [c] => 
          simp [List.foldl]
          have : c = '1' := by
            have : sy.get (sy.length - 1) = '1' := hpad.2.1
            simp [String.get, ←hd, ←String.length] at this
            simp at this
            exact this
          simp [this]
        | c :: c' :: cs =>
          simp [List.foldl]
          have c_zero : c = '0' := by
            have : c ∈ (sy.take (sy.length - 1)).data := by
              simp [String.take, ←hd, List.take]
              left; rfl
            exact hpad.2.2 c this
          simp [c_zero]
          clear c_zero
          generalize hz : 0 = z at *
          induction cs generalizing z with
          | nil =>
            simp [List.foldl]
            have : c' = '1' := by
              have : sy.get (sy.length - 1) = '1' := hpad.2.1
              simp [String.get, ←hd, ←String.length] at this
              simp at this
              exact this
            simp [this]
          | cons c'' cs'' ih2 =>
            simp [List.foldl]
            have : c' = '0' := by
              subst hz
              have : c' ∈ (sy.take (sy.length - 1)).data := by
                simp [String.take, ←hd, List.take]
                right; left; rfl
              exact hpad.2.2 c' this
            simp [this]
            exact ih2 rfl
    constructor
    · unfold modReduce toString
      split_ifs <;> try (intro i c hc; simp at hc; cases hc; try (left; rfl); try (right; rfl))
      intro i c hc
      clear h1 h2
      generalize hn : Str2Int sx % Str2Int sz = n' at hc
      clear hn
      induction n' using Nat.strong_induction_on with
      | _ n' ih' =>
        unfold toString at hc
        split_ifs at hc with hn0 hn1
        · simp at hc; cases hc; left; rfl
        · simp at hc; cases hc; right; rfl
        · simp at hc
          cases hc with
          | inl hc' => exact ih' _ (Nat.div_lt_self (by omega) (by omega)) hc'
          | inr hc' => simp at hc'; cases hc'; try (left; rfl); try (right; rfl)
    · simp [sy_one, Exp_int, modReduce]
      split_ifs
      · simp [toString]
      · simp [toString]
        generalize hn : Str2Int sx % Str2Int sz = n'
        clear hn h1 h2
        induction n' using Nat.strong_induction_on with
        | _ n' ih' =>
          unfold toString
          split_ifs with hn0 hn1
          · simp
          · simp
          · simp [Str2Int, List.foldl]
            rw [ih' (n' / 2) (Nat.div_lt_self (by omega) (by omega))]
            split_ifs <;> simp <;> ring
  · -- Recursive case: need to handle validity and correctness
    -- First establish validity of result
    have recValid : ValidBitString (ModExp sx (shiftRight sy) sz) := by
      apply ih
      · apply shiftRight_length_decreases
        apply isOne_false_of_not_zero <;> assumption
      · exact hx
      · intro i c hc
        unfold shiftRight at hc
        split_ifs at hc
        · simp at hc
        · have : c ∈ (sy.take (sy.length - 1)).data := by
            rw [String.get?_eq_data_get?] at hc
            exact String.mem_of_get? hc
          have : c ∈ sy.data := List.mem_of_mem_take this
          exact hy (String.mem_iff_get?.mpr ⟨_, String.get?_of_mem this⟩)
      · exact hz
      · unfold shiftRight
        split_ifs <;> simp [String.length_take] <;> omega
      · exact hsz_gt1
      · rfl
    have squaredValid : ValidBitString (modMul (ModExp sx (shiftRight sy) sz) (ModExp sx (shiftRight sy) sz) sz) := by
      unfold modMul modReduce
      split_ifs
      · exact Mul_spec _ _ recValid recValid |>.1
      · intro i c hc
        clear h1 h2
        generalize hn : _ = n' at hc
        clear hn
        induction n' using Nat.strong_induction_on generalizing i c with
        | _ n' ih' =>
          unfold toString at hc
          split_ifs at hc <;> (simp at hc; cases hc; try (left; rfl); try (right; rfl))
          cases hc with
          | inl hc' => exact ih' _ (Nat.div_lt_self (by omega) (by omega)) _ _ hc'
          | inr hc' => simp at hc'; cases hc'; try (left; rfl); try (right; rfl)
    split_ifs
    · exact squaredValid
    · unfold modMul modReduce
      split_ifs
      · exact Mul_spec _ _ squaredValid hx |>.1
      · intro i c hc
        clear h1 h2
        generalize hn : _ = n' at hc
        clear hn
        induction n' using Nat.strong_induction_on generalizing i c with
        | _ n' ih' =>
          unfold toString at hc
          split_ifs at hc <;> (simp at hc; cases hc; try (left; rfl); try (right; rfl))
          cases hc with
          | inl hc' => exact ih' _ (Nat.div_lt_self (by omega) (by omega)) _ _ hc'
          | inr hc' => simp at hc'; cases hc'; try (left; rfl); try (right; rfl)
-- </vc-proof>

end BignumLean