// <vc-preamble>
// Method to apply linear domain mapping transformation to input points
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): [No functional change; reviewed and kept] */
function map_value(v: real, oldDomain: seq<real>, newDomain: seq<real>): real
  requires |oldDomain| == 2
  requires |newDomain| == 2
  requires oldDomain[1] != oldDomain[0]
{
  var scale := (newDomain[1] - newDomain[0]) / (oldDomain[1] - oldDomain[0]);
  var offset := newDomain[0] - scale * oldDomain[0];
  offset + scale * v
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
  /* code modified by LLM (iteration 2): [Replaced sequence constructor with a while loop to resolve indexing error] */
  result := [];
  var i := 0;
  while i < |x|
    invariant |result| == i
    invariant 0 <= i <= |x|
    invariant forall k :: 0 <= k < |result| ==> result[k] == map_value(x[k], oldDomain, newDomain)
  {
    result := result + [map_value(x[i], oldDomain, newDomain)];
    i := i + 1;
  }
}
// </vc-code>
