// <vc-preamble>
// Method to apply linear domain mapping transformation to input points
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): use real literal 0.0 to avoid int/real mismatch */
lemma NondegenerateDiff(a: real, b: real)
  requires a != b
  ensures b - a != 0.0
{
  assert b - a != 0.0;
}

// </vc-helpers>

// <vc-spec>
method mapdomain(x: seq<real>, oldDomain: seq<real>, newDomain: seq<real>) returns (result: seq<real>)
  // Preconditions: old and new must be 2-element sequences, old domain non-degenerate
  requires |oldDomain| == 2
  requires |newDomain| == 2
  requires oldDomain[1] != oldDomain[0]  // Non-degenerate old domain
  
  // Postconditions: result has same length and follows linear transformation
  ensures |result| == |x|
  ensures forall i :: 0 <= i < |x| ==>
    var scale := (newDomain[1] - newDomain[0]) / (oldDomain[1] - oldDomain[0]);
    var offset := newDomain[0] - scale * oldDomain[0];
    result[i] == offset + scale * x[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): build result by filling an array and slicing to a sequence */
  var scale := (newDomain[1] - newDomain[0]) / (oldDomain[1] - oldDomain[0]);
  var offset := newDomain[0] - scale * oldDomain[0];
  var a := new real[|x|];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant forall j :: 0 <= j < i ==> a[j] == offset + scale * x[j]
  {
    a[i] := offset + scale * x[i];
    i := i + 1;
  }
  result := a[..];
}
// </vc-code>
