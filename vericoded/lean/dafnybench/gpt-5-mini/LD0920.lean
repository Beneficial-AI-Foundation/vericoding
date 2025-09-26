import Mathlib
-- <vc-preamble>
def min (x : Nat) (y : Nat) : Nat :=
if x ≤ y then x else y
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/-- Convenience helper: create an Array of zeros. -/
def mkZeros (n : Nat) : Array Int := Array.replicate n (0 : Int)

-- </vc-helpers>

-- <vc-definitions>
def sum (X_val : Array Int) (X_crd : Array Nat)
(v_val : Array Int) (v_crd : Array Nat)
(kX : Nat) (kV : Nat) (pX_end : Nat) (pV_end : Nat) : Int :=
let idxsX := List.map (fun m => m + kX) (List.range (if pX_end > kX then pX_end - kX else 0))
let idxsV := List.map (fun m => m + kV) (List.range (if pV_end > kV then pV_end - kV else 0))
idxsX.foldl (fun acc i =>
  idxsV.foldl (fun acc2 j =>
    match X_crd.get? i, v_crd.get? j with
    | some xi, some vj => if xi == vj then acc2 + (X_val.get! i) * (v_val.get! j) else acc2
    | _, _ => acc2) acc) (0 : Int)


def notin (y : Nat) (x : Array Nat) : Bool :=
not (x.toList.any (fun v => v == y))


def notin_seq (y : Nat) (x : Array Nat) : Bool :=
not (x.toList.any (fun v => v == y))


def index_seq (x : Nat) (y : Array Nat) : Nat :=
let idxs := List.range y.size
match idxs.find? (fun i => y.get! i == x) with
| some i => i
| none => y.size


def index (x : Nat) (y : Array Nat) : Nat :=
let idxs := List.range y.size
match idxs.find? (fun i => y.get! i == x) with
| some i => i
| none => y.size


def DSpMSpV (X_val : Array Int) (X_crd : Array Nat) (X_pos : Array Nat)
(X_crd1 : Array Nat) (X_len : Nat)
(v_val : Array Int) (v_crd : Array Nat) : Array Int :=
Array.replicate X_len (0 : Int)

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
  dsimp [DSpMSpV]
  simp

-- </vc-theorems>
