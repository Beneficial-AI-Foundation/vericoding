// <vc-preamble>
/**
 * Computes the logical NOT of each element in the input sequence according to NumPy semantics.
 * Uses NumPy's truthiness convention: zero is falsy (NOT zero = true), 
 * all non-zero values are truthy (NOT non-zero = false).
 */
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method LogicalNot(x: seq<real>) returns (result: seq<bool>)
  ensures |result| == |x|
  ensures forall i :: 0 <= i < |x| ==> result[i] == (x[i] == 0.0)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): assign to `result` directly from loop */
{
  var temp_result := new bool[|x|];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant temp_result.Length == |x|
    invariant forall j :: 0 <= j < i ==> temp_result[j] == (x[j] == 0.0)
  {
    temp_result[i] := (x[i] == 0.0);
    i := i + 1;
  }
  
  result := temp_result[..];
}
// </vc-code>
