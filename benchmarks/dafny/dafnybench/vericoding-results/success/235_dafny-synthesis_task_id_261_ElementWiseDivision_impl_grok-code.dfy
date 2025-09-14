

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ElementWiseDivision(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    requires forall i :: 0 <= i < |b| ==> b[i] != 0
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] / b[i]
// </vc-spec>
// <vc-code>
{
  if |a| == 0 {
    result := [];
  } else {
    var rest := ElementWiseDivision(a[1..], b[1..]);
    result := [a[0] / b[0]] + rest;
  }
}
// </vc-code>

