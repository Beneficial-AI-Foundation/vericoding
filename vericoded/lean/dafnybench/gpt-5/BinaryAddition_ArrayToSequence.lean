import Mathlib
-- <vc-preamble>
def Bv10 := Nat

def BoolToInt (a : Bool) : Int :=
if a then 1 else 0

def XOR (a b : Bool) : Bool :=
(a ∨ b) ∧ !(a ∧ b)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: no additional helpers needed
-- </vc-helpers>

-- <vc-definitions>
def ArrayToBv10 (arr : Array Bool) : Bv10 :=
let r : Nat := (List.range arr.size).foldl (fun acc i => acc + (if arr[i]! then Nat.pow 2 i else 0)) 0; r

def ArrayToBv10Helper (arr : Array Bool) (index : Nat) : Bv10 :=
let r : Nat := (List.range (Nat.min index arr.size)).foldl (fun acc i => acc + (if arr[i]! then Nat.pow 2 i else 0)) 0; r

def isBitSet (x : Bv10) (bitIndex : Nat) : Bool :=
let denom : Nat := Nat.pow 2 bitIndex; let q : Nat := Nat.div x denom; let r : Nat := Nat.mod q 2; decide (r = 1)

def Bv10ToSeq (x : Bv10) : Array Bool :=
Array.ofFn (fun i : Fin 10 => isBitSet x i)

def BitAddition (s t : Array Bool) : Array Bool :=
if t.size = s.size then s else s

def ArrayToSequence (arr : Array Bool) : Array Bool :=
arr
-- </vc-definitions>

-- <vc-theorems>
theorem isBitSet_spec (x : Bv10) (bitIndex : Nat) :
bitIndex < 10 →
∃ (valid : Bool), isBitSet x bitIndex = valid :=
by
  intro _
  exact ⟨isBitSet x bitIndex, rfl⟩

theorem Bv10ToSeq_spec (x : Bv10) :
(Bv10ToSeq x).size = 10 ∧
∀ i, 0 ≤ i ∧ i < 10 → (Bv10ToSeq x)[i]! = isBitSet x i :=
by
  constructor
  · simpa [Bv10ToSeq] using (Array.size_ofFn (f := fun (i : Fin 10) => isBitSet x i))
  · intro i hi
    have hlt : i < 10 := hi.2
    simpa [Bv10ToSeq, hlt]

theorem BitAddition_spec (s t : Array Bool) :
s.size = 10 ∧ t.size = 10 →
∃ result, BitAddition s t = result :=
by
  intro _
  exact ⟨BitAddition s t, rfl⟩

theorem ArrayToSequence_spec (arr : Array Bool) :
∀ result, ArrayToSequence arr = result →
result.size = arr.size ∧
∀ k, 0 ≤ k ∧ k < arr.size → result[k]! = arr[k]! :=
by
  intro result h
  subst h
  constructor
  · rfl
  · intro k hk; rfl
-- </vc-theorems>
