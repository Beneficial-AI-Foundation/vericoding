// <vc-preamble>
// Helper predicate to check if a sequence is a valid permutation of indices
predicate IsPermutation(indices: seq<int>, n: int)
{
  |indices| == n &&
  (forall i :: 0 <= i < n ==> 0 <= indices[i] < n) &&
  (forall i {:trigger i} :: 0 <= i < n ==> exists j {:trigger indices[j]} :: 0 <= j < n && indices[j] == i) &&
  (forall i, j :: 0 <= i < j < n ==> indices[i] != indices[j])
}

// Helper predicate to check if indices produce a sorted sequence
predicate IsSorted(a: seq<real>, indices: seq<int>)
  requires |indices| == |a|
  requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |a|
{
  forall i, j :: 0 <= i < j < |indices| ==> a[indices[i]] <= a[indices[j]]
}

// Helper predicate to check stability (equal elements maintain relative order)
predicate IsStable(a: seq<real>, indices: seq<int>)
  requires |indices| == |a|
  requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |a|
{
  forall i, j :: 0 <= i < j < |indices| && a[indices[i]] == a[indices[j]] ==> indices[i] < indices[j]
}

// Main argsort method specification
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method argsort(a: seq<real>) returns (indices: seq<int>)
  ensures |indices| == |a|
  ensures IsPermutation(indices, |a|)
  ensures IsSorted(a, indices)
  ensures IsStable(a, indices)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
