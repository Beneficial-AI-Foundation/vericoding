import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def Vector.replicate {α : Type*} (n : Nat) (v : Vector α m) : Vector (Vector α m) n :=
  Vector.mk (List.replicate n v.val) (by simp [List.length_replicate])

-- LLM HELPER
def Vector.map_with_index {α β : Type*} (f : α → Nat → β) (v : Vector α n) : Vector β n :=
  Vector.mk (v.val.mapIdx (fun i a => f a i)) (by simp [List.length_mapIdx])

def problem_spec {m n : Nat} (impl : Vector Float m → Vector Float n → Id (Vector (Vector Float m) n × Vector (Vector Float n) m)) 
    (x : Vector Float m) (y : Vector Float n) : Prop :=
  ⦃⌜True⌝⦄
  impl x y
  ⦃⇓result => 
    let (xv, yv) := result
    ⌜(∀ i : Fin n, ∀ j : Fin m, (xv.get i).get j = x.get j) ∧
     (∀ i : Fin m, ∀ j : Fin n, (yv.get i).get j = y.get j)⌝⦄

def meshgrid {m n : Nat} (x : Vector Float m) (y : Vector Float n) : 
    Id (Vector (Vector Float m) n × Vector (Vector Float n) m) := do
  let xv := Vector.replicate n x
  let yv_transposed : Vector (Vector Float n) m := 
    Vector.mk 
      (Array.toList (Array.range m).map (fun i => 
        Vector.mk (Array.toList (Array.range n).map (fun j => y.get ⟨j, Nat.lt_of_mem_range (Array.mem_range.mp (Array.mem_map.mp rfl).2)⟩)) (by simp [Array.size_range, Array.size_map])))
      (by simp [Array.size_range, Array.size_map])
  return (xv, yv_transposed)

-- LLM HELPER
theorem Vector.get_replicate {α : Type*} (n : Nat) (v : Vector α m) (i : Fin n) (j : Fin m) :
  ((Vector.replicate n v).get i).get j = v.get j := by
  simp [Vector.replicate, Vector.get, Vector.mk]
  rw [List.getElem_replicate]

-- LLM HELPER  
theorem Vector.get_transposed (y : Vector Float n) (i : Fin m) (j : Fin n) :
  let yv_transposed : Vector (Vector Float n) m := 
    Vector.mk 
      (Array.toList (Array.range m).map (fun i => 
        Vector.mk (Array.toList (Array.range n).map (fun j => y.get ⟨j, Nat.lt_of_mem_range (Array.mem_range.mp (Array.mem_map.mp rfl).2)⟩)) (by simp [Array.size_range, Array.size_map])))
      (by simp [Array.size_range, Array.size_map])
  (yv_transposed.get i).get j = y.get j := by
  simp [Vector.get, Vector.mk]
  rw [List.getElem_map]
  simp [Array.toList_range]
  rw [List.getElem_range]
  simp [Vector.get, Vector.mk]
  rw [List.getElem_map]
  simp [Array.toList_range]
  rw [List.getElem_range]

theorem correctness {m n : Nat} (x : Vector Float m) (y : Vector Float n) :
    problem_spec meshgrid x y := by
  simp [problem_spec]
  constructor
  · intro i j
    simp [meshgrid]
    rw [Vector.get_replicate]
  · intro i j  
    simp [meshgrid]
    rw [Vector.get_transposed]