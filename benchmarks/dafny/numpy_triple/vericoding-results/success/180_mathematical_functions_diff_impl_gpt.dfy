// <vc-preamble>
// Method to compute discrete differences between consecutive elements
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method numpy_diff(a: seq<real>) returns (result: seq<real>)
    // Input sequence must be non-empty
    requires |a| >= 1
    // Result has one less element than input
    ensures |result| == |a| - 1
    // Each result element is the difference between consecutive input elements
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i+1] - a[i]
    // Type preservation: result maintains the same numeric type as input (real)
// </vc-spec>
// <vc-code>
{
  var r: seq<real> := [];
  var i: int := 0;
  while i < |a| - 1
    invariant 0 <= i <= |a| - 1
    invariant |r| == i
    invariant forall k :: 0 <= k < |r| ==> r[k] == a[k+1] - a[k]
    decreases |a| - 1 - i
  {
    r := r + [a[i + 1] - a[i]];
    i := i + 1;
  }
  result := r;
}
// </vc-code>
