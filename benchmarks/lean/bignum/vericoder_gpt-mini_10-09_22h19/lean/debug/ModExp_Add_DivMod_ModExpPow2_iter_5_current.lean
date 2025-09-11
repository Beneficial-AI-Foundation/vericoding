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
def nat_bits_aux : Nat -> List Char
| 0 => []
| m+1 =>
  let q := (m+1) / 2
  let r := (m+1) % 2
  (if r = 1 then '1' else '0') :: nat_bits_aux q

-- LLM HELPER
def nat_bits (n : Nat) : List Char :=
  if n = 0 then ['0'] else List.reverse (nat_bits_aux n)

-- LLM HELPER
def nat_to_bin (n : Nat) : String := String.mk (nat_bits n)

-- LLM HELPER
def bits_to_nat (bs : List Char) : Nat :=
  bs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- LLM HELPER
theorem nat_bits_aux_chars (n : Nat) :
  ∀ c, c ∈ nat_bits_aux n → c = '0' ∨ c = '1' := by
  intro c
  induction n with
  | zero =>
    intro h
    simp [nat_bits_aux] at h
    contradiction
  | succ m ih =>
    intro h
    simp [nat_bits_aux] at h
    -- simplify membership for cons
    simp [List.mem_cons_iff] at h
    cases h with
    | inl heq =>
      let r := (m + 1) % 2
      by_cases hr : r = 1
      · -- head is '1'
        simp [hr] at heq
        -- heq : c = '1'
        exact Or.inr (Eq.symm heq)
      · -- head is '0'
        simp [hr] at heq
        exact Or.inl (Eq.symm heq)
    | inr htail =>
      exact ih htail

-- LLM HELPER
theorem nat_bits_chars (n : Nat) :
  ∀ c, c ∈ nat_bits n → c = '0' ∨ c = '1' := by
  intro c
  dsimp [nat_bits]
  by_cases h0 : n = 0
  · intro hmem
    simp [h0] at hmem
    -- the only element is '0'
    rcases hmem with rfl
    exact Or.inl rfl
  · intro hmem
    simp [h0] at hmem
    -- nat_bits n = reverse (nat_bits_aux n)
    -- use mem_reverse to move membership inside nat_bits_aux
    have mem := (List.mem_reverse.1 hmem)
    exact nat_bits_aux_chars n mem

-- LLM HELPER
theorem bits_to_nat_reverse_nat_bits_aux (n : Nat) :
  bits_to_nat (List.reverse (nat_bits_aux n)) = n := by
  induction n with
  | zero =>
    simp [nat_bits_aux, bits_to_nat]
  | succ m ih =>
    let r := (m + 1) % 2
    let q := (m + 1) / 2
    have hdecomp : nat_bits_aux (m+1) = (if r = 1 then '1' else '0') :: nat_bits_aux q := by
      rfl
    simp [hdecomp]
    -- reverse (a :: t) = reverse t ++ [a]
    dsimp [List.reverse]
    have : List.reverse ((if r = 1 then '1' else '0') :: nat_bits_aux q) =
           (List.reverse (nat_bits_aux q)) ++ [if r = 1 then '1' else '0'] := by
      simp [List.reverse]
    simp [this]
    -- foldl over append: foldl f 0 (l ++ [x]) = f (foldl f 0 l) x
    have foldl_append := List.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 (List.reverse (nat_bits_aux q)) [if r = 1 then '1' else '0']
    simp [bits_to_nat, foldl_append]
    -- apply induction hypothesis to (reverse (nat_bits_aux q))
    have ih' : bits_to_nat (List.reverse (nat_bits_aux q)) = q := by
      apply ih
    simp [ih']
    -- now we reduce to 2 * q + (if head = '1' then 1 else 0) = m+1
    by_cases hr : r = 1
    · simp [hr]
      -- r = 1, so (if head = '1' then 1 else 0) = 1
      have : (if '1' = '1' then 1 else 0) = 1 := by simp
      simp [this]
      -- r = 1 and q = (m+1)/2 so 2*q + 1 = m+1 holds by division/mod arithmetic
      have : 2 * q + 1 = m + 1 := by
        -- using definition of q and r, when r = 1
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
def nat_bits_aux : Nat -> List Char
| 0 => []
| m+1 =>
  let q := (m+1) / 2
  let r := (m+1) % 2
  (if r = 1 then '1' else '0') :: nat_bits_aux q

-- LLM HELPER
def nat_bits (n : Nat) : List Char :=
  if n = 0 then ['0'] else List.reverse (nat_bits_aux n)

-- LLM HELPER
def nat_to_bin (n : Nat) : String := String.mk (nat_bits n)

-- LLM HELPER
def bits_to_nat (bs : List Char) : Nat :=
  bs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- LLM HELPER
theorem nat_bits_aux_chars (n : Nat) :
  ∀ c, c ∈ nat_bits_aux n → c = '0' ∨ c = '1' := by
  intro c
  induction n with
  | zero =>
    intro h
    simp [nat_bits_aux] at h
    contradiction
  | succ m ih =>
    intro h
    simp [nat_bits_aux] at h
    -- simplify membership for cons
    simp [List.mem_cons_iff] at h
    cases h with
    | inl heq =>
      let r := (m + 1) % 2
      by_cases hr : r = 1
      · -- head is '1'
        simp [hr] at heq
        -- heq : c = '1'
        exact Or.inr (Eq.symm heq)
      · -- head is '0'
        simp [hr] at heq
        exact Or.inl (Eq.symm heq)
    | inr htail =>
      exact ih htail

-- LLM HELPER
theorem nat_bits_chars (n : Nat) :
  ∀ c, c ∈ nat_bits n → c = '0' ∨ c = '1' := by
  intro c
  dsimp [nat_bits]
  by_cases h0 : n = 0
  · intro hmem
    simp [h0] at hmem
    -- the only element is '0'
    rcases hmem with rfl
    exact Or.inl rfl
  · intro hmem
    simp [h0] at hmem
    -- nat_bits n = reverse (nat_bits_aux n)
    -- use mem_reverse to move membership inside nat_bits_aux
    have mem := (List.mem_reverse.1 hmem)
    exact nat_bits_aux_chars n mem

-- LLM HELPER
theorem bits_to_nat_reverse_nat_bits_aux (n : Nat) :
  bits_to_nat (List.reverse (nat_bits_aux n)) = n := by
  induction n with
  | zero =>
    simp [nat_bits_aux, bits_to_nat]
  | succ m ih =>
    let r := (m + 1) % 2
    let q := (m + 1) / 2
    have hdecomp : nat_bits_aux (m+1) = (if r = 1 then '1' else '0') :: nat_bits_aux q := by
      rfl
    simp [hdecomp]
    -- reverse (a :: t) = reverse t ++ [a]
    dsimp [List.reverse]
    have : List.reverse ((if r = 1 then '1' else '0') :: nat_bits_aux q) =
           (List.reverse (nat_bits_aux q)) ++ [if r = 1 then '1' else '0'] := by
      simp [List.reverse]
    simp [this]
    -- foldl over append: foldl f 0 (l ++ [x]) = f (foldl f 0 l) x
    have foldl_append := List.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 (List.reverse (nat_bits_aux q)) [if r = 1 then '1' else '0']
    simp [bits_to_nat, foldl_append]
    -- apply induction hypothesis to (reverse (nat_bits_aux q))
    have ih' : bits_to_nat (List.reverse (nat_bits_aux q)) = q := by
      apply ih
    simp [ih']
    -- now we reduce to 2 * q + (if head = '1' then 1 else 0) = m+1
    by_cases hr : r = 1
    · simp [hr]
      -- r = 1, so (if head = '1' then 1 else 0) = 1
      have : (if '1' = '1' then 1 else 0) = 1 := by simp
      simp [this]
      -- r = 1 and q = (m+1)/2 so 2*q + 1 = m+1 holds by division/mod arithmetic
      have : 2 * q + 1 = m + 1 := by
        -- using definition of q and r, when r = 1
-- </vc-code>

end BignumLean