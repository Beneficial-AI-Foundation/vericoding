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
· -- Case: s2.data.isEmpty
  constructor
  · intro i c hget
    simp only at hget
    have : "0".get? i = some c := hget
    cases i
    · simp [String.get?] at this
      injection this with eq_c
      right
      exact eq_c
    · simp [String.get?] at this
  · simp [Str2Int]
    cases h_empty : s2.data
    · simp
    · contradiction
· -- Case: ¬s2.data.isEmpty
  have aux_valid : ValidBitString (mulAux s1 s2.data.reverse 0) := by
    unfold mulAux
    split
    · intro i c hget
      simp at hget
      cases hget
      right
      rfl
    · apply (Add_spec _ _ _ _).1
      · unfold shiftLeft mulByBit
        split
        · intro i c hget
          cases String.append_get? _ _ i with
          | inl h => exact h1 h
          | inr h => 
            simp [String.mk, List.replicate] at h
            split at h <;> simp at h
            split at h
            · injection h with eq_c
              right
              exact eq_c
            · exact (Option.none_ne_some _ h).elim
        · intro i c hget
          simp [String.get?] at hget
          cases hget
          right
          rfl
      · apply (Add_spec _ _ _ _).1 <;> try assumption
        intro i c hget
        simp at hget
        cases hget
        right
        rfl
  have aux_value : Str2Int (mulAux s1 s2.data.reverse 0) = Str2Int s1 * Str2Int s2 := by
    unfold mulAux
    split
    · simp [Str2Int]
      have : s2.data = [] := by
        cases s2.data
        · rfl
        · contradiction
      rw [this]
      simp [Str2Int]
    · simp [Add_spec, shiftLeft, mulByBit, Str2Int]
      split
      · simp [Str2Int]
        rfl
      · simp [Str2Int]
        ring
  exact ⟨aux_valid, aux_value⟩
-- </vc-proof>

end BignumLean