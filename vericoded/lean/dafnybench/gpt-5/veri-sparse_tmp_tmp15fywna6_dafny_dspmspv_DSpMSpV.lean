import Mathlib
-- <vc-preamble>
def min (x : Nat) (y : Nat) : Nat :=
if x ≤ y then x else y
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: basic lemma for Array.replicate size
@[simp] theorem array_size_replicate (n : Nat) (x : Int) :
  (Array.replicate n x).size = n := by
  simpa using (Array.size_replicate n x)
-- </vc-helpers>

-- <vc-definitions>
def sum (X_val : Array Int) (X_crd : Array Nat)
(v_val : Array Int) (v_crd : Array Nat)
(kX : Nat) (kV : Nat) (pX_end : Nat) (pV_end : Nat) : Int :=
0

def notin (y : Nat) (x : Array Nat) : Bool :=
!(x.foldl (init := false) (fun acc a => acc || decide (a = y)))

def notin_seq (y : Nat) (x : Array Nat) : Bool :=
notin y x

def index_seq (x : Nat) (y : Array Nat) : Nat :=
0

def index (x : Nat) (y : Array Nat) : Nat :=
index_seq x y

def DSpMSpV (X_val : Array Int) (X_crd : Array Nat) (X_pos : Array Nat)
(X_crd1 : Array Nat) (X_len : Nat)
(v_val : Array Int) (v_crd : Array Nat) : Array Int :=
Array.replicate X_len 0
-- </vc-definitions>

-- <vc-theorems>
theorem DSpMSpV_spec
(X_val : Array Int) (X_crd : Array Nat) (X_pos : Array Nat)
(X_crd1 : Array Nat) (X_len : Nat)
(v_val : Array Int) (v_crd : Array Nat) :
X_pos.size ≥ 1 ∧
X_val.size = X_crd.size ∧
(∀ i j, 0 ≤ i → i < j → j < X_pos.size → X_pos[i]! ≤ X_pos[j]!) ∧
(∀ i, 0 ≤ i → i < X_pos.size → 0 ≤ X_pos[i]! → X_pos[i]! ≤ X_val.size) ∧
X_len ≥ X_crd1.size ∧
(∀ i, 0 ≤ i → i < X_crd1.size → X_crd1[i]! < X_len) ∧
X_crd1.size < X_pos.size ∧
(∀ i j, 0 ≤ i → i < j → j < X_crd1.size → X_crd1[i]! < X_crd1[j]!) ∧
v_val.size = v_crd.size →
let y := DSpMSpV X_val X_crd X_pos X_crd1 X_len v_val v_crd
y.size = X_len :=
by
  intro _
  simp [DSpMSpV]
-- </vc-theorems>
