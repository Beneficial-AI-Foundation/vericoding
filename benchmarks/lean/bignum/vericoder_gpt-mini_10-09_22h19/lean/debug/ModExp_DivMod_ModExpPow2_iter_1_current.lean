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

def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
  sorry

axiom ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz

-- <vc-helpers>
-- LLM HELPER
def nat_to_bin_aux : Nat → List Char → List Char
  | 0, acc => acc
  | m+1, acc =>
    let m := m+1
    let digit := if m % 2 = 1 then '1' else '0'
    nat_to_bin_aux (m / 2) (digit :: acc)

-- LLM HELPER
def nat_to_bin_list (n : Nat) : List Char :=
  if n = 0 then ['0'] else nat_to_bin_aux n []

-- LLM HELPER
def nat_to_bin_string (n : Nat) : String :=
  String.mk (nat_to_bin_list n)

-- LLM HELPER
theorem nat_to_bin_aux_append (n : Nat) (acc : List Char) :
    nat_to_bin_aux n acc = (nat_to_bin_aux n []) ++ acc := by
  induction n using Nat.strong_induction_on with
  | ih k =>
    cases k with
    | zero =>
      simp [nat_to_bin_aux]
    | succ k' =>
      let m := k'.succ
      -- m = k
      simp [nat_to_bin_aux]
      have h := ih (m / 2) (by
        apply Nat.div_lt_self (Nat.succ_pos k')
        apply Nat.succ_pos) -- (m / 2) < m
      -- `h` states nat_to_bin_aux (m/2) acc' = nat_to_bin_aux (m/2) [] ++ acc'
      -- instantiate with acc' = (if m % 2 = 1 then '1' else '0') :: acc
      have h' : nat_to_bin_aux (m / 2) ((if m % 2 = 1 then '1' else '0') :: acc) =
                nat_to_bin_aux (m / 2) [] ++ ((if m % 2 = 1 then '1' else '0') :: acc) := by
        apply h
      simp [h']

-- LLM HELPER
theorem nat_to_bin_list_eq_aux (n : Nat) :
  nat_to_bin_list n = if n = 0 then ['0'] else nat_to_bin_aux n [] := by
  simp [nat_to_bin_list]

-- LLM HELPER
theorem nat_to_bin_string_valid (n : Nat) : ValidBitString (nat_to_bin_string n) := by
  dsimp [nat_to_bin_string, nat_to_bin_list]
  split
  · -- case n = 0
    by_cases h : n = 0
    · simp [h]
      intro i c hc
      simp at hc
      -- only one char '0'
      rcases i with (_ | i)
      · simp [String.mk, List.get?] at hc
        simp at hc
        injection hc with hc1
        subst hc1
        simp
      · simp at hc
      done
    · -- n ≠ 0
      have : nat_to_bin_aux n [] = nat_to_bin_aux n [] := rfl
      let s := String.mk (nat_to_bin_aux n [])
      intro i c hc
      have : s.data.get? i = some c := by
        exact hc
      -- all characters produced are '0' or '1' by construction
      -- prove by induction on the list nat_to_bin_aux n []
      have L := nat_to_bin_aux n []
      -- show all characters are '0' or '1'
      let rec all_bits : List Char → Prop
        | [] => True
        | ch :: rest => (ch = '0' ∨ ch = '1') ∧ all_bits rest
      -- we prove the stronger claim that each produced char is '0' or '1'
      -- by observing how digits are constructed
      have digits_prop : ∀ m acc, nat_to_bin_aux m acc = (nat_to_bin_aux m []) ++ acc := by
        intro m acc
        exact (nat_to_bin_aux_append m acc)
      -- from digits construction each digit is '0' or '1'
      -- do a simple induction to show every char is '0' or '1'
      let rec aux_prop : ∀ l, (∀ i c, (String.mk l).data.get? i = some c → (c = '0' ∨ c = '1'))
        | [] => by
          intro i c hc
          simp at hc
      ·
        intro l
        induction l with
        | nil => simp
        | cons ch tl ih =>
          intro i c hget
          simp [String.mk] at hget
          rcases i with
          | zero =>
            simp at hget
            injection hget with hch
            subst hch
            simp
          | succ i' =>
            apply ih
            simpa using hget
      apply aux_prop (nat_to_bin_aux n [])
  done

-- LLM HELPER
theorem Str2Int_nat_to_bin_eq (n : Nat) : Str2Int (nat_to_bin_string n) = n := by
  dsimp [nat_to_bin_string, nat_to_bin_list]
  by_cases hzero : n = 0
  · simp [hzero, Str2Int]; -- for "0" string we compute foldl over single '0' => 0
    dsimp [Str2Int]
    -- compute foldl over ['0']
    have : String.mk ['0'] = String.mk ['0'] := rfl
    simp [String.mk]
    -- manual computation: foldl starting at 0, ch = '0' gives 2*0 + 0 = 0
    simp [Str2Int]
  · -- n > 0
    -- we will prove by strong induction on n that Str2Int (String.mk (nat_to_bin_aux n [])) = n
    apply Nat.strong_induction_on n
    intro k ih
    dsimp at hzero
    have hkpos : 0 < k := Nat.pos_of_ne_zero hzero.symm
    -- Expand nat_to_bin_aux for k
    simp [nat_to_bin_aux]
    -- Let d = k % 2 and q = k / 2
    let q := k / 2
    let d := k % 2
    have k_eq : k = 2 * q + d := by
      rw [Nat.div_add_mod]; simp
    -- Show aux structure: nat_to_bin_aux k [] = nat_to_bin_aux q [] ++ [if d = 1 then '1' else '0']
    have aux_decomp : nat_to_bin_aux k [] = (nat_to_bin_aux q []) ++ [if d = 1 then '1' else '0'] := by
      -- unfold once
      simp [nat_to_bin_aux]
      -- now apply the append lemma with appropriate instantiation
      have := nat_to_bin_aux_append q ([if d = 1 then '1' else '0'])
      -- instantiate for q and that acc; but nat_to_bin_aux_append gives: nat_to_bin_aux q acc = nat_to_bin_aux q [] ++ acc
      -- we used that to deduce the decomposition
      simp [nat_to_bin_aux] at this
      -- but we already matched the pattern above; we can just finish by symmetry
      exact this
    -- Now compute Str2Int on the concatenation
    have : Str2Int (String.mk (nat_to_bin_aux k [])) =
            2 * Str2Int (String.mk (nat_to_bin_aux q [])) + (if d = 1 then 1 else 0) := by
      -- Str2Int of list ++ [last] equals 2 * Str2Int of prefix + last_bit
      -- we prove this by unfolding Str2Int definition (foldl) and properties of list concatenation
      dsimp [Str2Int]
      -- Work with list form
      let Lq := nat_to_bin_aux q []
      have : (String.mk (Lq ++ [if d = 1 then '1' else '0'])).data = Lq ++ [if d = 1 then '1' else '0'] := rfl
      -- compute foldl over concatenation: foldl over prefix then incorporate last digit
      -- Use induction on Lq to show foldl property
      let rec foldl_concat : ∀ (l : List Char) (a : Nat),
        (l ++ [if d = 1 then '1' else '0']).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) a =
        let mid := l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) a in
        2 * mid + (if d = 1 then 1 else 0)
        | [], a => by simp
        | ch :: tl, a =>
          have IH := foldl_concat tl (2 * a + (if ch = '1' then 1 else 0))
          simp [List.foldl] at *
          calc
            (ch :: tl ++ [if d = 1 then '1' else '0']).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) a
              = (tl ++ [if d = 1 then '1' else '0']).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) (2 * a + (if ch = '1' then 1 else 0)) := rfl
            _ = 2 * (tl.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) (2 * a + (if ch = '1' then 1 else 0))) + (if d = 1 then 1 else 0) := by simp [IH]
      -- apply with a = 0
      have := foldl_concat (nat_to_bin_aux q []) 0
      simp at this
      exact this
    -- Apply induction hypothesis to q (note q < k)
    have q_lt : q < k := Nat.div_lt_self (Nat.pos_of_ne_zero hzero.symm) (by decide)
    have IHq := ih q q_lt
    specialize IHq
    -- IHq gives Str2Int (String.mk (nat_to_bin_aux q [])) = q
    -- Conclude
    calc
      Str2Int (String.mk (nat_to_bin_aux k [])) = 2 * Str2Int (String.mk (nat_to_bin_aux q [])) + (if d = 1 then 1 else 0) := this
      _ = 2 * q + (if d = 1 then 1 else 0) := by rw [IHq]
      _ = k := by
        have := Nat.div_add_mod k 2
        simp [Nat.div_mod_eq_iff] at this
        -- directly use div_add_mod
        exact (by
          rw [Nat.div_add_mod]
          simp)
  -- conclude the nonzero case
  simp [nat_to_bin_list] at hzero
  simp [nat_to_bin_list]
  -- we handled both cases in the branches above
  done
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExp (sx sy sz : String) : String :=
  let x := Str2Int sx
  let y := Str2Int sy
  let z := Str2Int sz
  let r := Exp_int x y % z
  nat_to_bin_string r
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
  -- proof proceeds by unfolding ModExp and applying helper theorems about conversion
  dsimp [ModExp]
  let x := Str2Int sx
  let y := Str2Int sy
  let z := Str2Int sz
  let r := Exp_int x y % z
  have v := nat_to_bin_string_valid r
  have e := Str2Int_nat_to_bin_eq r
  exact ⟨v, e⟩
-- </vc-theorem>
-- <vc-proof>
-- (All proofs are provided above in the helpers and theorem blocks.)
-- This block intentionally left empty because full structured proofs appear in the helper/theorem sections.
-- </vc-proof>

end BignumLean