/-
QuickSelect algorithm with multiset specifications.
Ported from Dafny specification at:
dafny/benchmarks/dafny-bench_specs/atomizer_supported/Dafny_tmp_tmp0wu8wmfr_Heimaverkefni 8_H8_spec.dfy

This module contains specifications for partitioning and QuickSelect algorithm
using multisets to find the k-th smallest element.
-/

import dafnybench.Multiset

namespace DafnyBenchmarks

/-- Represents a partition result -/
structure PartitionResult where
  pre : List Int
  pivot : Int
  post : List Int

/-- Partition a list around a pivot element -/
def partition (lst : List Int) (h : lst ≠ []) : PartitionResult :=
  match lst with
  | [] => ⟨[], 0, []⟩  -- This case should never happen due to h
  | p :: rest =>
    let pre := rest.filter (· ≤ p)
    let post := rest.filter (· > p)
    ⟨pre, p, post⟩

/-- QuickSelect algorithm to find the k-th smallest element -/
def quickSelect (lst : List Int) (k : Nat) (h : lst ≠ [] ∧ k < lst.length) : PartitionResult :=
  let part := partition lst h.1
  if h : part.pre.length = k then
    part
  else if h2 : k < part.pre.length then
    if hp : part.pre ≠ [] ∧ k < part.pre.length then
      let subResult := quickSelect part.pre k hp
      ⟨subResult.pre, subResult.pivot, subResult.post ++ [part.pivot] ++ part.post⟩
    else
      part  -- Should not reach here
  else
    if k > part.pre.length && part.post ≠ [] then
      let newK := k - part.pre.length - 1
      if hp : part.post ≠ [] ∧ newK < part.post.length then
        let subResult := quickSelect part.post newK hp
        ⟨part.pre ++ [part.pivot] ++ subResult.pre, subResult.pivot, subResult.post⟩
      else
        part  -- Should not reach here
    else
      part
termination_by sorry

/-- Specification for partition -/
theorem partition_spec (lst : List Int) (h : lst ≠ []) :
    let part := partition lst h
    part.pivot ∈ lst ∧
    lst.toMultiset = (part.pre ++ [part.pivot] ++ part.post).toMultiset ∧
    (∀ z ∈ part.pre, z ≤ part.pivot) ∧
    (∀ z ∈ part.post, z ≥ part.pivot) := by
  sorry

/-- Specification for QuickSelect -/
theorem quickSelect_spec (lst : List Int) (k : Nat) (h : lst ≠ [] ∧ k < lst.length) :
    let result := quickSelect lst k h
    result.pivot ∈ lst ∧
    lst.toMultiset = (result.pre ++ [result.pivot] ++ result.post).toMultiset ∧
    result.pre.length = k ∧
    (∀ z ∈ result.pre, z ≤ result.pivot) ∧
    (∀ z ∈ result.post, z ≥ result.pivot) := by
  sorry

end DafnyBenchmarks
