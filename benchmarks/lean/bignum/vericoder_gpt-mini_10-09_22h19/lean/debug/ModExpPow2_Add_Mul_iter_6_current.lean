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
def bits_rev : Nat -> List Char
| 0     => []
| n + 1 =>
  let m := n + 1
  let r := m % 2
  let q := m / 2
  let c := if r = 1 then '1' else '0'
  c :: bits_rev q

-- LLM HELPER
def list_to_nat (l : List Char) : Nat :=
  l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- LLM HELPER
def string_of_chars (l : List Char) : String :=
  l.foldl (fun s c => s.push c) ""

-- LLM HELPER
def nat_to_str : Nat -> String
| 0     => "0"
| n + 1 =>
  let l := (bits_rev (n + 1)).reverse
  string_of_chars l

-- LLM HELPER
theorem string_of_chars_data {l : List Char} :
  (string_of_chars l).data = l := by
  induction l with
  | nil =>
    simp [string_of_chars]
  | cons hd tl ih =>
    simp [string_of_chars, List.foldl]
    -- foldl on cons: foldl f init (hd :: tl) = foldl f (f init hd) tl
    -- we show (foldl push "" (hd :: tl)).data = hd :: tl by reducing stepwise
    have : (List.foldl (fun s c => s.push c) ("" : String) (hd :: tl)) =
           (List.foldl (fun s c => s.push c) ("" : String).push hd) tl := by
      rfl
    -- now use that pushing preserves data by induction
    simp [String.push, ih]

-- LLM HELPER
theorem bits_rev_only_bits : ∀ n c, c ∈ (bits_rev n) → (c = '0' ∨ c = '1') := by
  intro n
  induction n with
  | zero =>
    intro c h
    simp [bits_rev] at h
    exact False.elim (List.not_mem_nil _ h)
  | succ k ih =>
    intro c h
    simp [bits_rev] at h
    cases h with
    | head => simp [*] at head; subst head; simp
    | tail => apply ih; assumption

-- LLM HELPER
theorem string_of_chars_only_bits (l : List Char) :
  (∀ c, c ∈ l → (c = '0' ∨ c = '1')) →
  ∀ i ch, (string_of_chars l).get? i = some ch → (ch = '0' ∨ ch = '1') := by
  -- We reduce to membership in data list, then use the assumption about elements of l.
  intro H i ch h
  -- use the fact that (string_of_chars l).data = l
  have : (string_of_chars l).data = l := by
    apply string_of_chars_data
  -- relate get? to data: get? returning ch implies ch ∈ s.data
  -- prove this by unfolding definitions of get? on String which indexes into .data
  have mem : ch ∈ (string_of_chars l).data := by
    -- s.get? i = some ch implies ch is in the backing data list
    -- We can reason by cases on i through the definition of String.get? which is based on .data
    -- Rather than delve into internals, we can use induction on l to establish the relationship.
    revert i ch h
    induction l with
    | nil =>
      intros i ch h
      simp [string_of_chars] at h
      simp [String.get?] at h
      contradiction
    | cons hd tl ihl =>
      intros i ch h
      simp [string_of_chars] at *
      -- foldl push "" (hd :: tl) = (foldl push "" tl).push hd ... reduce and analyze get?
      -- We use a case analysis on the position: if it points to the last character or earlier ones.
      -- Although get? uses String.Pos, the implementation ensures that any returned character is one of the underlying data.
      -- We proceed by converting to data with the previously proven equality.
      have data_eq : (string_of_chars (hd :: tl)).data = hd :: tl := by
        apply string_of_chars_data
      -- Now deduce membership from equality and get? result
      -- Convert get? result into membership: since the character equals some element at some index, it is in the list.
      -- Use a simple membership extraction: if s.get? i = some ch then ch ∈ s.data.
      -- We claim this follows from the implementation of get?. We encode it as:
      match (String.get? (string_of_chars (hd :: tl)) i) with
      | some c' =>
        have := Option.some.inj h
        -- From h we get ch = c'
        injection h with hch
        subst hch
        -- conclude membership using data_eq and the fact that c' is one of hd :: tl (by construction)
        simp [data_eq]; apply List.mem_cons_self
      | none => contradiction
  -- now apply H on the membership converted to l
  have mem_in_l : ch ∈ l := by
    simpa [this] using mem
  exact H ch mem_in_l

-- LLM HELPER
theorem nat_to_str_valid : ∀ n, ValidBitString (nat_to_str n) := by
  intro n
  cases n with
  | zero => exact str_zero_valid
  | succ n' =>
    -- nat_to_str (n' + 1) builds from bits_rev (n' + 1).reverse
    let l := (bits_rev (n' + 1)).reverse
    have Hbits : ∀ c, c ∈ l → (c = '0' ∨ c = '1' ) := by
      intro c hc
      have : c ∈ (bits_rev (n' + 1)) := by
        rwa [List.mem_reverse] at hc
      exact bits_rev_only_bits _ _ this
    -- use string_of_chars_only_bits to lift to ValidBitString
    intros i ch h
    apply string_of_chars_only_bits l Hbits i ch h

-- LLM HELPER
theorem list_to_nat_reverse_bits_rev (n : Nat) :
  list_to_nat ((bits_rev n).reverse) = n := by
  induction n with
  | zero => simp [bits_rev, list_to_nat]
  | succ k ih =>
    let m := k + 1
    have : bits_rev (m) = (if m % 2 = 1 then '1' else '0') :: bits_rev (m / 2) := rfl
    simp [bits_rev, list_to_nat] at *
    -- compute by cases on remainder
    have rfl_case : (m % 2 = 0 ∨ m % 2 = 1) := by
      have : m % 2 < 2 := Nat.mod_lt m (by decide)
      cases Nat.mod m 2 <; simp at this; cases this <; simp
      all_goals exact Or.inl rfl
    -- Instead of branching, use the division identity: m = 2*(m/2) + (m%2)
    have m_eq : m = 2 * (m / 2) + (m % 2) := by
      exact Nat.div_add_mod m 2
    -- Now use IH on (m / 2)
    have ih' : list_to_nat ((bits_rev (m / 2)).reverse) = (m / 2) := by
      apply ih
    -- compute:
    have : list_to_nat ((bits_rev m).reverse) =
           2 * list_to_nat ((bits_rev (m / 2)).reverse) + (if m % 2 = 1 then 1 else 0) := by
      -- expand definitions and use fold/reverse properties
      simp [list_to_nat]
      -- unfold reverse cons structure
      have : (bits_rev m).reverse = (bits_rev (m / 2)).reverse ++ [if m % 2 = 1 then '1' else '0'] := by
        simp [bits_rev]; exact (List.reverse_cons (if m % 2 = 1 then '1' else '0') (bits_rev (m / 2))).symm
      rw [this]
      simp [List.foldl_append]
      -- fold over the single-element list yields 2 * acc + bit
      simp
    rw [this, ih']
    -- now finish using m_eq and the fact that (if m%2 =1 then 1 else 0) = m % 2
    have bit_eq : (if m % 2 = 1 then 1 else 0) = m % 2 := by
      have h : m % 2 ∈ {0,1} := by
        apply Nat.mod_lt; decide
      cases (m % 2) with
      | zero => simp
      | succ _ => -- this can only be 1
        have : m % 2 = 1 := by
          -- Since m%2 < 2 and nonzero -> must be 1
          have lt := Nat.mod_lt m (by decide)
          cases m % 2 <; simp at lt; contradiction <|> trivial
          simp
        simp [this]
    rwa [bit_eq, m_eq]

-- LLM HELPER
theorem nat_to_str_correct : ∀ n, Str2Int (nat_to_str n) = n := by
  intro n
  induction n with
  | zero => simp [nat_to_str, Str2Int, list_to_nat]; rfl
  | succ k ih =>
    -- nat_to_str (k + 1) = string_of_chars ((bits_rev (k+1)).reverse)
    let l := (bits_rev (k + 1)).reverse
    have data_eq : (string_of_chars l).data = l := by apply string_of_chars_data
    simp [nat_to_str]
    -- Str2Int uses s.data.foldl same as list_to_nat
    have : Str2Int (string_of_chars l) = list_to_nat l := by
      simp [Str2Int, list_to_nat, data_eq]
    rw [this]
    -- apply bits_rev correctness
    have bits_correct := list_to_nat_reverse_bits_rev (k + 1)
    -- note that list_to_nat ((bits_rev (k+1)).reverse) = k+1
    exact bits_correct
-- </vc-helpers>

-- <vc-spec>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
  -- produce a canonical string representing the required natural number
  nat_to_str ((Exp_int (Str2Int sx) (Str2Int sy)) % Str2Int sz)
-- </vc-code>

-- <vc-theorem>
theorem ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
  -- keep the statement unchanged; proof provided in vc-proof
  exact by
    have
-- </vc-theorem>
end BignumLean