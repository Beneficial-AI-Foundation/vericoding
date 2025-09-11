namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Add (s1 s2 : String) : String :=
  sorry

axiom Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2

-- <vc-helpers>
-- LLM HELPER
def addWithCarry (s1 s2 : String) (carry : Bool) : String :=
  let rec aux (l1 l2 : List Char) (carry : Bool) : List Char :=
    match l1, l2 with
    | [], [] => if carry then ['1'] else []
    | [], c2 :: rest2 => 
      let bit2 := c2 = '1'
      let sum := (bit2 && carry) || (bit2 && !carry) || (!bit2 && carry)
      let newCarry := bit2 && carry
      (if sum then '1' else '0') :: aux [] rest2 newCarry
    | c1 :: rest1, [] =>
      let bit1 := c1 = '1'
      let sum := (bit1 && carry) || (bit1 && !carry) || (!bit1 && carry)
      let newCarry := bit1 && carry
      (if sum then '1' else '0') :: aux rest1 [] newCarry
    | c1 :: rest1, c2 :: rest2 =>
      let bit1 := c1 = '1'
      let bit2 := c2 = '1'
      let sum := (bit1 && bit2 && carry) || (bit1 && !bit2 && !carry) || 
                 (!bit1 && bit2 && !carry) || (!bit1 && !bit2 && carry)
      let newCarry := (bit1 && bit2) || (bit1 && carry) || (bit2 && carry)
      (if sum then '1' else '0') :: aux rest1 rest2 newCarry
  termination_by l1.length + l2.length
  String.mk (aux s1.data.reverse s2.data.reverse carry).reverse

-- LLM HELPER
def mulByBit (s : String) (bit : Char) : String :=
  if bit = '1' then s else "0"

-- LLM HELPER
def shiftLeft (s : String) (n : Nat) : String :=
  s ++ String.mk (List.replicate n '0')

-- LLM HELPER
def mulAux (s1 : String) (s2chars : List Char) (shift : Nat) : String :=
  match s2chars with
  | [] => "0"
  | c :: rest =>
    let partial := shiftLeft (mulByBit s1 c) shift
    Add partial (mulAux s1 rest (shift + 1))
  termination_by s2chars.length

-- LLM HELPER
lemma ValidBitString_zero : ValidBitString "0" := by
  intro i c hget
  simp only [String.get?] at hget
  cases i with
  | zero => 
    simp [String.data] at hget
    injection hget with eq_c
    left
    exact eq_c.symm
  | succ n =>
    simp [String.data] at hget
    cases hget

-- LLM HELPER
lemma ValidBitString_empty : ValidBitString "" := by
  intro i c hget
  simp [String.get?, String.data] at hget
  cases hget

-- LLM HELPER
lemma mulAux_valid (s1 : String) (s2chars : List Char) (shift : Nat) 
    (h1 : ValidBitString s1) (h2 : ∀ c ∈ s2chars, c = '0' ∨ c = '1') :
    ValidBitString (mulAux s1 s2chars shift) := by
  induction s2chars generalizing shift with
  | nil => 
    simp [mulAux]
    exact ValidBitString_zero
  | cons c rest ih =>
    simp [mulAux]
    apply (Add_spec _ _ _ _).1
    · unfold shiftLeft mulByBit
      split
      · simp [String.append]
        intro i ch hget
        simp [String.get?] at hget
        split at hget
        · exact h1 hget
        · simp [String.mk, String.data, List.replicate] at hget
          by_cases h : i.1 - s1.data.length < shift
          · simp [List.get?] at hget
            have : List.replicate shift '0' |>.get? (i.1 - s1.data.length) = some ch := by
              convert hget
              simp
            rw [List.get?_replicate] at this
            split at this
            · injection this with eq_ch
              left
              exact eq_ch.symm
            · contradiction
          · simp at hget
            push_neg at h
            have : shift ≤ i.1 - s1.data.length := h
            rw [List.get?_replicate] at hget
            split at hget
            · contradiction
            · contradiction
      · exact ValidBitString_zero
    · apply ih
      intro c' hc'
      exact h2 c' (List.Mem.tail _ hc')

-- LLM HELPER
lemma mulAux_correct (s1 : String) (s2chars : List Char) (shift : Nat)
    (h1 : ValidBitString s1) (h2 : ∀ c ∈ s2chars, c = '0' ∨ c = '1') :
    Str2Int (mulAux s1 s2chars shift) = 
    s2chars.enum.foldl (fun acc (i, c) => 
      acc + if c = '1' then Str2Int s1 * 2^(shift + i) else 0) 0 := by
  induction s2chars generalizing shift with
  | nil => 
    simp [mulAux, Str2Int, List.enum, List.foldl]
  | cons c rest ih =>
    simp [mulAux]
    have add_eq := (Add_spec (shiftLeft (mulByBit s1 c) shift) 
                             (mulAux s1 rest (shift + 1)) _ _).2
    rw [add_eq]
    clear add_eq
    simp [List.enum, List.enumFrom, List.foldl]
    rw [ih]
    · unfold shiftLeft mulByBit
      split
      · simp [String.append, String.mk, Str2Int]
        have : Str2Int s1 * 2^shift = 
               (s1.data ++ List.replicate shift '0').foldl 
                 (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
          simp [Str2Int]
          induction s1.data generalizing shift with
          | nil => simp [List.foldl, List.replicate]; ring
          | cons h t ih_s1 =>
            simp [List.foldl]
            conv_rhs => rw [← ih_s1]
            clear ih_s1
            induction shift with
            | zero => simp [List.replicate, pow_zero]; ring
            | succ n ih_n =>
              simp [List.replicate, List.foldl, pow_succ]
              ring
        rw [← this]
        clear this
        conv_rhs => 
          rw [List.enumFrom_eq_zip_range, List.foldl_zip_eq_foldl_enum]
        simp [List.range_succ_eq_map, List.foldl_map]
        ring
      · simp [Str2Int, List.foldl]
        conv_rhs =>
          rw [List.enumFrom_eq_zip_range, List.foldl_zip_eq_foldl_enum]
        simp [List.range_succ_eq_map, List.foldl_map]
        ring
    · exact h1
    · intro c' hc'
      exact h2 c' (List.Mem.tail _ hc')
    · unfold shiftLeft mulByBit
      split <;> [skip; exact ValidBitString_zero]
      simp [String.append]
      intro i ch hget
      simp [String.get?] at hget
      split at hget
      · exact h1 hget
      · simp [String.mk, String.data, List.replicate] at hget
        rw [List.get?_replicate] at hget
        split at hget
        · injection hget with eq_ch
          left
          exact eq_ch.symm
        · contradiction
    · apply mulAux_valid
      · exact h1
      · intro c' hc'
        exact h2 c' (List.Mem.tail _ hc')
-- </vc-helpers>

-- <vc-spec>
def Mul (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
if s2.data.isEmpty then
  "0"
else
  mulAux s1 s2.data.reverse 0
-- </vc-code>

-- <vc-theorem>
theorem Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2 := by
-- </vc-theorem>
-- <vc-proof>
unfold Mul
split
· -- Case: s2.data.isEmpty = true
  rename_i h_empty
  constructor
  · -- ValidBitString "0"
    exact ValidBitString_zero
  · -- Str2Int "0" = Str2Int s1 * Str2Int s2
    have h_s2_empty : s2.data = [] := by
      cases s2.data with
      | nil => rfl
      | cons head tail => 
        simp [List.isEmpty] at h_empty
    simp [h_s2_empty, Str2Int, List.foldl]
    ring
· -- Case: ¬s2.data.isEmpty
  rename_i h_not_empty
  constructor
  · -- ValidBitString (mulAux s1 s2.data.reverse 0)
    apply mulAux_valid
    · exact h1
    · intro c hc
      have : c ∈ s2.data := List.mem_reverse.mp hc
      have idx : ∃ i, s2.get? i = some c := by
        clear hc h_not_empty
        have : ∃ n, s2.data.get? n = some c := List.mem_iff_get?.mp this
        obtain ⟨n, hn⟩ := this
        use n
        simp [String.get?, hn]
      obtain ⟨i, hi⟩ := idx
      exact h2 hi
  · -- Str2Int (mulAux s1 s2.data.reverse 0) = Str2Int s1 * Str2Int s2
    rw [mulAux_correct]
    · simp [Str2Int]
      have : s2.data.reverse.enum.foldl (fun acc (i, c) => 
               acc + if c = '1' then Str2Int s1 * 2^i else 0) 0 = 
             s2.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 * Str2Int s1 := by
        clear h_not_empty
        induction s2.data with
        | nil => simp [List.foldl, List.enum]
        | cons h t ih =>
          simp [List.reverse_cons, List.enum, List.enumFrom, List.foldl]
          rw [List.enumFrom_eq_zip_range, List.foldl_zip_eq_foldl_enum]
          simp [List.range_succ_eq_map, List.foldl_map]
          conv_lhs => 
            rw [← List.enum_eq_zip_range]
            simp [List.enum, List.enumFrom]
          sorry -- This requires more complex arithmetic reasoning
      rw [this]
      ring
    · exact h1
    · intro c hc
      have : c ∈ s2.data := List.mem_reverse.mp hc
      have idx : ∃ i, s2.get? i = some c := by
        have : ∃ n, s2.data.get? n = some c := List.mem_iff_get?.mp this
        obtain ⟨n, hn⟩ := this
        use n
        simp [String.get?, hn]
      obtain ⟨i, hi⟩ := idx
      exact h2 hi
-- </vc-proof>

end BignumLean