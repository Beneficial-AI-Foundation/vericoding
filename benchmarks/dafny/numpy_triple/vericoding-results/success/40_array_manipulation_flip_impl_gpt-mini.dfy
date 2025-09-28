// <vc-preamble>
// Method that reverses the order of elements in a sequence
// Corresponds to numpy.flip for 1D arrays
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): recursive reverse function with specification */
function rev(m: seq<real>): seq<real>
  ensures |rev(m)| == |m|
  ensures forall i :: 0 <= i < |m| ==> rev(m)[i] == m[|m| - 1 - i]
  decreases |m|
{
  if |m| == 0 then [] else rev(m[1..]) + [m[0]]
}
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
{
  /* code modified by LLM (iteration 3): call rev helper to produce reversed sequence */
  result := rev(m);
}
// </vc-code>
