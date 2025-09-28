// <vc-preamble>
// Method to compute discrete differences between consecutive elements
// </vc-preamble>

// <vc-helpers>
function abs(x: real): real { if x >= 0.0 then x else -x }

/* helper modified by LLM (iteration 4): Keep abs function but fix method body */
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
  /* code modified by LLM (iteration 4): Fixed array to sequence conversion */
  result := [];
  var i := 0;
  while i < |a| - 1
    invariant 0 <= i <= |a| - 1
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == a[j+1] - a[j]
  {
    result := result + [a[i+1] - a[i]];
    i := i + 1;
  }
}
// </vc-code>
