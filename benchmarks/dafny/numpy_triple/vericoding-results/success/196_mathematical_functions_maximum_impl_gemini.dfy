// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): [fixed 'unresolved identifier' error by using function name in ensures clauses] */
function MaxReal(a: real, b: real): real
  ensures MaxReal(a, b) >= a && MaxReal(a, b) >= b
  ensures MaxReal(a, b) == a || MaxReal(a, b) == b
{
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
  /* code modified by LLM (iteration 2): [no logical changes needed for this iteration] */
  var res := new real[|x1|];
  var i := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |x1| == |x2|
    invariant forall j :: 0 <= j < i ==> res[j] == MaxReal(x1[j], x2[j])
  {
    res[i] := MaxReal(x1[i], x2[i]);
    i := i + 1;
  }
  result := res[..];
}
// </vc-code>
