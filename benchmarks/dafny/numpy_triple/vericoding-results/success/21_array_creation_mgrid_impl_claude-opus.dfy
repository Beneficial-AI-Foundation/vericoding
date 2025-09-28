// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method mgrid(start: real, stop: real, step: real) returns (result: seq<real>)
  // Input constraints
  requires step > 0.0
  requires start < stop
  requires ((stop - start) / step).Floor >= 0  // Ensure non-negative sequence length
  
  // Output constraints  
  ensures var n := ((stop - start) / step).Floor;
          n >= 0 && |result| == n
  ensures forall i :: 0 <= i < |result| ==>
    result[i] == start + (i as real) * step
  ensures forall i :: 0 <= i < |result| ==>
    result[i] < stop
// </vc-spec>
// <vc-code>
{
  var n := ((stop - start) / step).Floor;
  result := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == start + (j as real) * step
    invariant forall j :: 0 <= j < i ==> result[j] < stop
  {
    var value := start + (i as real) * step;
    result := result + [value];
    i := i + 1;
  }
}
// </vc-code>
