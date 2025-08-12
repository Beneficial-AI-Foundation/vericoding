import Plausible
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Basic
import Testing.PlausibleUtils

namespace Testing.PlausibleExamples

open Plausible Testing.PlausibleUtils

section ListProperties

example : ∀ (xs ys : List Nat), xs ++ ys = ys ++ xs := by
  plausible

example : ∀ (xs : List Nat), xs.reverse.reverse = xs := by
  plausible

example : ∀ (xs : List Nat) (x : Nat), (x :: xs).length = xs.length + 1 := by
  plausible

#eval checkWithMsg "List append is associative" <|
  ∀ (xs ys zs : List Nat), (xs ++ ys) ++ zs = xs ++ (ys ++ zs)

#eval checkWithMsg "List length distributes over append" <|
  ∀ (xs ys : List Nat), (xs ++ ys).length = xs.length + ys.length

end ListProperties

section MatrixProperties

example : ∀ (m : Matrix (Fin 3) (Fin 3) Int), m + 0 = m := by
  plausible

example : ∀ (m n : Matrix (Fin 2) (Fin 2) Int), m + n = n + m := by
  plausible

end MatrixProperties

section FunctionProperties

def isEven (n : Nat) : Bool := n % 2 = 0

example : ∀ n : Nat, isEven n → isEven (n + 2) := by
  plausible

example : ∀ n : Nat, isEven n ↔ ¬isEven (n + 1) := by
  plausible

def collatz (n : Nat) : Nat :=
  if n ≤ 1 then 1
  else if n % 2 = 0 then n / 2
  else 3 * n + 1

example : ∀ n : Nat, n > 0 → ∃ k : Nat, k < 100 ∧ 
  (Nat.iterate collatz k n = 1) := by
  plausible (config := { numInst := 20 })

end FunctionProperties

section SpecValidation

structure Rectangle where
  width : Nat
  height : Nat
deriving Repr

def Rectangle.area (r : Rectangle) : Nat := r.width * r.height

def Rectangle.perimeter (r : Rectangle) : Nat := 2 * (r.width + r.height)

instance : Sampleable Rectangle where
  sample := do
    let w ← Sampleable.sample (α := Nat)
    let h ← Sampleable.sample (α := Nat)
    pure { width := w, height := h }

instance : PrintableProp Rectangle where
  printProp r := s!"Rectangle {{ width := {r.width}, height := {r.height} }}"

example : ∀ r : Rectangle, r.area = 0 ↔ (r.width = 0 ∨ r.height = 0) := by
  plausible

example : ∀ r : Rectangle, r.perimeter ≥ 2 * r.area.sqrt := by
  plausible (config := { numInst := 50 })

def isSquare (r : Rectangle) : Bool := r.width = r.height

#eval checkWithMsg "Squares have minimum perimeter for given area" <|
  ∀ r1 r2 : Rectangle, 
    r1.area = r2.area → 
    isSquare r1 → 
    r1.perimeter ≤ r2.perimeter

end SpecValidation

section CounterexampleFinding

def buggySort (xs : List Nat) : List Nat :=
  match xs with
  | [] => []
  | [x] => [x]
  | x :: y :: rest => 
    if x ≤ y then x :: buggySort (y :: rest)
    else y :: buggySort (x :: rest)

example : ∀ xs : List Nat, (buggySort xs).Sorted (· ≤ ·) := by
  plausible (config := { numInst := 100 })

def almostPrime (n : Nat) : Bool :=
  n > 1 && (List.range n).filter (fun d => d > 1 && n % d = 0) |>.length ≤ 2

example : ∀ n : Nat, almostPrime n → 
  ∀ d : Nat, d > 1 → d < n → n % d = 0 → almostPrime d := by
  plausible

end CounterexampleFinding

section CustomGenerators

structure Point3D where
  x : Int
  y : Int
  z : Int
deriving Repr

instance : Sampleable Point3D where
  sample := do
    let x ← Sampleable.sample (α := Int)
    let y ← Sampleable.sample (α := Int)
    let z ← Sampleable.sample (α := Int)
    pure { x := x, y := y, z := z }

instance : PrintableProp Point3D where
  printProp p := s!"Point3D {{ x := {p.x}, y := {p.y}, z := {p.z} }}"

def Point3D.distance (p q : Point3D) : Nat :=
  ((p.x - q.x).natAbs ^ 2 + (p.y - q.y).natAbs ^ 2 + (p.z - q.z).natAbs ^ 2).sqrt

example : ∀ p q : Point3D, p.distance q = q.distance p := by
  plausible

example : ∀ p q r : Point3D, 
  p.distance r ≤ p.distance q + q.distance r := by
  plausible (config := { numInst := 100 })

end CustomGenerators

end Testing.PlausibleExamples