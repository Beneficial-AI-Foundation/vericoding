import Mathlib
-- <vc-preamble>
def Bv10 := Nat

def BoolToInt (a : Bool) : Int :=
if a then 1 else 0

def XOR (a b : Bool) : Bool :=
(a ∨ b) ∧ ¬(a ∧ b)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[inline] def arrGetD {α} (a : Array α) (i : Nat) (d : α) : α :=
  (a.get? i).getD d
-- </vc-helpers>

-- <vc-definitions>
def ArrayToBv10 (arr : Array Bool) : Bv10 :=
List.foldl
    (fun (acc : Nat) (i : Nat) => acc + (if arrGetD arr i false then Nat.pow 2 i else 0))
    (0 : Nat)
    (List.range 10)

def ArrayToBv10Helper (arr : Array Bool) (index : Nat) : Bv10 :=
List.foldl
    (fun (acc : Nat) (i : Nat) => acc + (if arrGetD arr i false then Nat.pow 2 i else 0))
    (0 : Nat)
    (List.range (Nat.min index 10))

def ArrayToSequence (arr : Array Bool) : Array Bool :=
Array.ofFn (fun i : Fin 10 => arrGetD arr i.val false)

def isBitSet (x : Bv10) (bitIndex : Nat) : Bool :=
let xN : Nat := x; decide (((xN / Nat.pow 2 bitIndex) % 2) = 1)

def Bv10ToSeq (x : Bv10) : Array Bool :=
Array.ofFn (fun i : Fin 10 => isBitSet x i.val)

def BitAddition (s t : Array Bool) : Array Bool :=
Array.ofFn (fun i : Fin 10 => XOR (arrGetD s i.val false) (arrGetD t i.val false))

def BinaryAddition (s t : Array Bool) : Array Bool :=
BitAddition s t
-- </vc-definitions>

-- <vc-theorems>
theorem BinaryAddition_spec (s t : Array Bool) :
s.size = 10 ∧ t.size = 10 →
let result := BinaryAddition s t
result.size = 10 ∧ result = BitAddition s t :=
by
  intro _
  let result := BinaryAddition s t
  have hsize : result.size = 10 := by
    simp [result, BinaryAddition, BitAddition]
  have hres : result = BitAddition s t := by
    simp [result, BinaryAddition]
  exact And.intro hsize hres
-- </vc-theorems>
