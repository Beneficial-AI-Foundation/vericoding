// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): No changes to helper needed. */
function ComputeBitwiseAndElement(a: bv32, b: bv32): bv32 {
  a & b
}
// </vc-helpers>

// <vc-spec>
method BitwiseAnd(x1: seq<bv32>, x2: seq<bv32>) returns (result: seq<bv32>)
  // Arrays must have the same length
  requires |x1| == |x2|
  
  // Result has same length as inputs
  ensures |result| == |x1|
  
  // Each element is the bitwise AND of corresponding input elements
  ensures forall i :: 0 <= i < |result| ==> result[i] == (x1[i] & x2[i])
  
  // Bitwise AND result is always <= both inputs (for non-negative integers)
  ensures forall i :: 0 <= i < |result| ==> result[i] <= x1[i]
  ensures forall i :: 0 <= i < |result| ==> result[i] <= x2[i]
  
  // Annihilator property: if either input is zero, result is zero
  ensures forall i :: 0 <= i < |result| ==> (x1[i] == 0 || x2[i] == 0) ==> result[i] == 0
  
  // Idempotence: x & x = x
  ensures forall i :: 0 <= i < |result| ==> (x1[i] == x2[i] ==> result[i] == x1[i])
  
  // Commutativity property (implicitly satisfied by bitwise AND)
  ensures forall i :: 0 <= i < |result| ==> result[i] == (x2[i] & x1[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Corrected type mismatch for `result` by converting array to sequence. */
{
  var tempResult := new bv32[|x1|];
  var i := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant forall k :: 0 <= k < i ==> tempResult[k] == (x1[k] & x2[k])
  {
    tempResult[i] := ComputeBitwiseAndElement(x1[i], x2[i]);
    i := i + 1;
  }
  result := tempResult[..];
}
// </vc-code>
