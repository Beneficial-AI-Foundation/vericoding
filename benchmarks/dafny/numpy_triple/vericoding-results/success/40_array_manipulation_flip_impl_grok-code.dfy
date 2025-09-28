// <vc-preamble>
// Method that reverses the order of elements in a sequence
// Corresponds to numpy.flip for 1D arrays
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): No helpers needed */
// </vc-helpers>

// <vc-spec>
method numpy_flip(m: seq<real>) returns (result: seq<real>)
    // Size preservation: output has same length as input
    ensures |result| == |m|
    // Element mapping: element at position i in result equals 
    // element at position (n-1-i) in input
    ensures forall i :: 0 <= i < |m| ==> result[i] == m[|m| - 1 - i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Added loop invariants for size and element mapping to prove postconditions */
{
  var rev: seq<real> := [];
  var i: int := |m|;
  var n: int := |m|;
  while i > 0
    decreases i
    invariant 0 <= i <= n
    invariant |rev| == n - i
    invariant forall k :: 0 <= k < |rev| ==> rev[k] == m[n - 1 - k]
  {
    i := i - 1;
    rev := rev + [m[i]];
  }
  result := rev;
}
// </vc-code>
