// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): predicate for checking non-zero element at index */
predicate IsNonZero(a: seq<real>, i: int) {
  0 <= i < |a| && a[i] != 0.0
}

/* helper modified by LLM (iteration 2): return last element of sequence or -1 if empty */
function LastOrMinusOne(s: seq<int>): int {
  if |s| == 0 then -1 else s[|s|-1]
}
// </vc-helpers>

// <vc-spec>
method argwhere(a: seq<real>) returns (indices: seq<int>)
  // All returned indices are valid and correspond to non-zero elements
  ensures forall i :: 0 <= i < |indices| ==> 
            0 <= indices[i] < |a| && a[indices[i]] != 0.0
  
  // Completeness: all non-zero elements in input have their indices in result
  ensures forall j :: 0 <= j < |a| && a[j] != 0.0 ==> 
            j in indices
  
  // No duplicate indices in the result
  ensures forall i, j :: 0 <= i < j < |indices| ==> 
            indices[i] != indices[j]
  
  // Indices are ordered according to their position in the original array
  ensures forall i, j :: 0 <= i < j < |indices| ==> 
            indices[i] < indices[j]
  
  // Result is empty if and only if all elements in input are zero
  ensures (|indices| == 0) <==> 
          (forall k :: 0 <= k < |a| ==> a[k] == 0.0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): scan array and collect indices of non-zero elements with strong invariants */
  indices := [];
  var i := 0;
  while i < |a|
    decreases |a| - i
    invariant 0 <= i <= |a|
    invariant forall k :: 0 <= k < |indices| ==> 0 <= indices[k] < i && a[indices[k]] != 0.0
    invariant forall p, q :: 0 <= p < q < |indices| ==> indices[p] < indices[q]
    invariant forall j :: 0 <= j < i && a[j] != 0.0 ==> j in indices
    invariant (|indices| == 0) <==> (forall j :: 0 <= j < i ==> a[j] == 0.0)
  {
    if a[i] != 0.0 {
      indices := indices + [i];
    }
    i := i + 1;
  }
}
// </vc-code>
