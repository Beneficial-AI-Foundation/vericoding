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
  -- We use the Add axiom to build the result
  have h_aux : ∀ c ∈ s2.data.reverse, c = '0' ∨ c = '1' := by
    intro c hc
    have : c ∈ s2.data := List.mem_reverse.mp hc
    clear hc
    induction s2.data with
    | nil => simp at this
    | cons head tail ih =>
      cases this with
      | head h_eq =>
        have : s2.get? 0 = some head := by
          simp [String.get?, String.data]
        rw [← h_eq]
        exact h2 this
      | tail h_in =>
        have idx : ∃ i, String.mk tail |>.get? i = some c := by
          clear ih h_not_empty
          induction tail generalizing c with
          | nil => simp at h_in
          | cons h t ih_t =>
            cases h_in with
            | head h_eq =>
              use 0
              simp [String.get?, String.data, h_eq]
            | tail h_in' =>
              obtain ⟨i, hi⟩ := ih_t h_in'
              use i + 1
              simp [String.get?, String.data]
              exact hi
        obtain ⟨i, hi⟩ := idx
        have : s2.get? (i + 1) = some c := by
          simp [String.get?, String.data] at hi ⊢
          exact hi
        exact h2 this
  -- Prove validity using induction on the structure
  have valid_result : ValidBitString (mulAux s1 s2.data.reverse 0) := by
    induction s2.data.reverse generalizing s1 with
    | nil =>
      simp [mulAux]
      exact ValidBitString_zero
    | cons c rest ih =>
      simp [mulAux]
      have vc : c = '0' ∨ c = '1' := h_aux c (List.Mem.head _)
      have vrest : ∀ c' ∈ rest, c' = '0' ∨ c' = '1' := 
        fun c' hc' => h_aux c' (List.Mem.tail _ hc')
      have partial_valid : ValidBitString (shiftLeft (mulByBit s1 c) 0) := by
        unfold shiftLeft mulByBit
        cases vc with
        | inl h0 =>
          simp [h0]
          exact ValidBitString_zero
        | inr h1 =>
          simp [h1]
          simp [String.append, String.mk, List.replicate]
          exact h1
      have rest_valid : ValidBitString (mulAux s1 rest 1) := by
        clear ih partial_valid
        induction rest generalizing s1 with
        | nil =>
          simp [mulAux]
          exact ValidBitString_zero
        | cons c' rest' ih' =>
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
                split at hget <;> simp at hget
                split at hget <;> simp at hget
                injection hget with eq_ch
                left
                exact eq_ch.symm
            · exact ValidBitString_zero
          · apply ih'
            intro c'' hc''
            exact vrest c'' (List.Mem.tail _ hc'')
      exact (Add_spec _ _ partial_valid rest_valid).1
  constructor
  · exact valid_result
  · -- For the arithmetic property, we rely on the Add axiom's correctness
    -- The proof would follow by structural induction showing that
    -- mulAux computes the correct multiplication via repeated addition
    -- Since Add is axiomatized to be correct, the result follows
    induction s2.data.reverse generalizing s1 with
    | nil =>
      simp [mulAux, Str2Int, List.foldl]
      have : s2.data.reverse = [] := by simp at h_not_empty; assumption
      have : s2.data = [] := by simp [← this]
      simp [this] at h_not_empty
    | cons c rest ih =>
      simp [mulAux]
      have add_correct := (Add_spec _ _ _ _).2
      simp at add_correct
      rw [add_correct]
      · unfold shiftLeft mulByBit
        split
        · simp [Str2Int, String.append, String.data, List.foldl_append]
          simp [List.replicate, List.foldl]
          ring
        · simp [Str2Int, String.data, List.foldl]
      · unfold shiftLeft mulByBit
        split
        · intro i ch hget
          simp [String.get?, String.append] at hget
          split at hget
          · exact h1 hget
          · simp [String.mk, String.data, List.replicate] at hget
            split at hget <;> simp at hget
            split at hget <;> simp at hget
            injection hget with eq_ch
            left
            exact eq_ch.symm
        · exact ValidBitString_zero
      · clear ih add_correct valid_result
        induction rest generalizing s1 with
        | nil =>
          simp [mulAux]
          exact ValidBitString_zero
        | cons c' rest' ih' =>
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
                split at hget <;> simp at hget
                split at hget <;> simp at hget
                injection hget with eq_ch
                left
                exact eq_ch.symm
            · exact ValidBitString_zero
          · apply ih'
-- </vc-proof>

end BignumLean