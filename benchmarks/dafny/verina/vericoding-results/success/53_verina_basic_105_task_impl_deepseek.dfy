// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

function multiplyElements(a: seq<int>, b: seq<int>): seq<int>
  requires |a| == |b|
  ensures |multiplyElements(a, b)| == |a|
  ensures forall i :: 0 <= i < |a| ==> multiplyElements(a, b)[i] == a[i] * b[i]
{
  if |a| == 0 then []
  else [a[0] * b[0]] + multiplyElements(a[1..], b[1..])
}

// </vc-helpers>

// <vc-spec>
method ArrayProduct(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> result[i] == a[i] * b[i]
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == a[j] * b[j]
  {
    result := result + [a[i] * b[i]];
    i := i + 1;
  }
}
// </vc-code>
