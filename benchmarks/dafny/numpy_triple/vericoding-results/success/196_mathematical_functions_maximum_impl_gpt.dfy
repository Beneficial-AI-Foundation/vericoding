// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): implemented real max function and lemma with basic properties */
function maxr(a: real, b: real): real { if a >= b then a else b }

/* helper modified by LLM (iteration 2): lemma stating max properties */
lemma MaxrProps(a: real, b: real)
  ensures maxr(a,b) >= a && maxr(a,b) >= b
  ensures maxr(a,b) == a || maxr(a,b) == b
{
  if a >= b {
    assert maxr(a,b) == a;
    assert maxr(a,b) >= a;
    assert maxr(a,b) >= b;
  } else {
    assert maxr(a,b) == b;
    assert maxr(a,b) >= b;
    assert maxr(a,b) >= a;
  }
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
  /* code modified by LLM (iteration 2): iteratively build result using element-wise max without lemma calls */
  result := x1;
  var i: int := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |result| == |x1|
    invariant forall j :: 0 <= j < i ==> result[j] == (if x1[j] >= x2[j] then x1[j] else x2[j])
    decreases |x1| - i
  {
    var r: real := if x1[i] >= x2[i] then x1[i] else x2[i];
    result := result[i := r];
    i := i + 1;
  }
}
// </vc-code>
