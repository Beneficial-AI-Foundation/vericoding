// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Max(a: real, b: real): real {
  /* helper modified by LLM (iteration 2): no change */
  if a >= b then a else b
}
// </vc-helpers>

// <vc-spec>
method Maximum(x1: seq<real>, x2: seq<real>) returns (result: seq<real>)
  // Arrays must have the same length
  requires |x1| == |x2|
  // Result has the same length as input arrays
  ensures |result| == |x1|
  // Each element is the maximum of corresponding elements from x1 and x2
  ensures forall i :: 0 <= i < |result| ==> 
    result[i] == if x1[i] >= x2[i] then x1[i] else x2[i]
  // Each result element is greater than or equal to both input elements
  ensures forall i :: 0 <= i < |result| ==> 
    result[i] >= x1[i] && result[i] >= x2[i]
  // Each result element equals one of the corresponding input elements
  ensures forall i :: 0 <= i < |result| ==> 
    result[i] == x1[i] || result[i] == x2[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed type mismatch from array<real> to seq<real> */
  var n := |x1|;
  var res_seq := new real[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> res_seq[j] == Max(x1[j], x2[j])
  {
    res_seq[i] := Max(x1[i], x2[i]);
    i := i + 1;
  }
  return res_seq[..];
}
// </vc-code>
