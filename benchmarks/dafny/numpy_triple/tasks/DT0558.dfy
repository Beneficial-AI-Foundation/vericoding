// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ArgPartition(a: seq<real>, kth: int) returns (indices: seq<int>)
  // Input requirements
  requires 0 <= kth < |a|
  requires |a| > 0
  
  // Output guarantees
  ensures |indices| == |a|
  
  // The indices form a valid permutation of 0..|a|-1
  ensures forall i :: 0 <= i < |a| ==> 0 <= indices[i] < |a|
  ensures forall i :: 0 <= i < |a| ==> exists j {:trigger indices[j]} :: 0 <= j < |a| && indices[j] == i
  ensures forall i, j :: 0 <= i < |a| && 0 <= j < |a| && i != j ==> indices[i] != indices[j]
  
  // Partition property: all elements before kth position are <= kth element
  ensures forall i :: 0 <= i < kth ==> a[indices[i]] <= a[indices[kth]]
  
  // Partition property: all elements after kth position are >= kth element  
  ensures forall i :: kth < i < |a| ==> a[indices[kth]] <= a[indices[i]]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
