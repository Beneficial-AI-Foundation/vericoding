// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function IsStrictlyIncreasing(xs: seq<int>): bool { forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j] }

function IsStrictlyDecreasing(xs: seq<int>): bool { forall i, j :: 0 <= i < j < |xs| ==> xs[i] > xs[j] }
// </vc-helpers>

// <vc-spec>
method monotonic(xs: seq<int>) returns (result: bool)

  requires |xs| > 0

  ensures result <==> (forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j]) || (forall i, j :: 0 <= i < j < |xs| ==> xs[i] > xs[j])
// </vc-spec>
// <vc-code>
{
  var increasing := IsStrictlyIncreasing(xs);
  var decreasing := IsStrictlyDecreasing(xs);
  result := increasing || decreasing;
}
// </vc-code>
