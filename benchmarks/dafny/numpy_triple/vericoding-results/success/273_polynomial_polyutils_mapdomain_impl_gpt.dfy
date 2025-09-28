// <vc-preamble>
// Method to apply linear domain mapping transformation to input points
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): define scale and offset for linear domain mapping */
function linScale(oldDomain: seq<real>, newDomain: seq<real>): real
  requires |oldDomain| == 2
  requires |newDomain| == 2
  requires oldDomain[1] != oldDomain[0]
{
  (newDomain[1] - newDomain[0]) / (oldDomain[1] - oldDomain[0])
}

/* helper modified by LLM (iteration 2): compute offset using scale */
function linOffset(oldDomain: seq<real>, newDomain: seq<real>): real
  requires |oldDomain| == 2
  requires |newDomain| == 2
  requires oldDomain[1] != oldDomain[0]
{
  newDomain[0] - linScale(oldDomain, newDomain) * oldDomain[0]
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
  /* code modified by LLM (iteration 2): implement linear transform via loop to avoid comprehension parse issues and ensure postconditions */
  var s := linScale(oldDomain, newDomain);
  var o := linOffset(oldDomain, newDomain);

  // Help the prover connect helpers to the spec's local definitions
  assert s == (newDomain[1] - newDomain[0]) / (oldDomain[1] - oldDomain[0]);
  assert o == newDomain[0] - s * oldDomain[0];

  var r: seq<real> := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> r[j] == o + s * x[j]
    decreases |x| - i
  {
    r := r + [o + s * x[i]];
    i := i + 1;
  }
  result := r;
}
// </vc-code>
