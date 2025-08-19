import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def Vector.replicate {α : Type*} (n : Nat) (v : Vector α m) : Vector (Vector α m) n :=
  Vector.mk (List.replicate n v.toList)

-- LLM HELPER
def Vector.map_with_index {α β : Type*} (f : α → Nat → β) (v : Vector α n) : Vector β n :=
  Vector.mk (v.toList.mapIdx (fun i a => f a i))

def problem_spec {m n : Nat} (impl : Vector Float m → Vector Float n → Id (Vector (Vector Float m) n × Vector (Vector Float m) n)) 
    (x : Vector Float m) (y : Vector Float n) : Prop :=
  ⦃⌜True⌝⦄
  impl x y
  ⦃⇓result => 
    let (xv, yv) := result
    ⌜(∀ i : Fin n, ∀ j : Fin m, (xv.get i).get j = x.get j) ∧
     (∀ i : Fin n, ∀ j : Fin m, (yv.get i).get j = y.get i)⌝⦄

def meshgrid {m n : Nat} (x : Vector Float m) (y : Vector Float n) : 
    Id (Vector (Vector Float m) n × Vector (Vector Float m) n) := do
  let xv := Vector.replicate n x
  let yv := Vector.map_with_index (fun yi _ => Vector.mk (List.replicate m yi)) y
  return (xv, yv)

-- LLM HELPER
theorem Vector.get_replicate {α : Type*} (n : Nat) (v : Vector α m) (i : Fin n) (j : Fin m) :
  ((Vector.replicate n v).get i).get j = v.get j := by
  simp [Vector.replicate, Vector.get, Vector.mk]
  simp [List.get_replicate]

-- LLM HELPER
theorem List.get_replicate {α : Type*} (n : Nat) (l : List α) (i : Fin n) (j : Fin l.length) :
  (List.replicate n l)[i.val]![j.val] = l[j.val]! := by
  rw [List.getElem_replicate]

-- LLM HELPER
theorem Vector.get_map_with_index {α β : Type*} (f : α → Nat → β) (v : Vector α n) (i : Fin n) :
  (v.map_with_index f).get i = f (v.get i) i := by
  simp [Vector.map_with_index, Vector.get, Vector.mk]
  rw [List.getElem_mapIdx]

theorem correctness {m n : Nat} (x : Vector Float m) (y : Vector Float n) :
    problem_spec meshgrid x y := by
  simp [problem_spec]
  simp [wpD]
  constructor
  · intro i j
    simp [meshgrid]
    rw [Vector.get_replicate]
  · intro i j
    simp [meshgrid]
    rw [Vector.get_map_with_index]
    simp [Vector.mk, Vector.get]
    rw [List.getElem_replicate]