// <vc-preamble>
function Power(base: int, exponent: int): int
    requires exponent >= 0
{
    if exponent == 0 then 1
    else base * Power(base, exponent-1)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method PowerOfListElements(l: seq<int>, n: int) returns (result: seq<int>)
    requires n >= 0
    ensures |result| == |l|
    ensures forall i :: 0 <= i < |l| ==> result[i] == Power(l[i], n)
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == Power(l[k], n)
  {
    var p := Power(l[i], n);
    result := result + [p];
    i := i + 1;
  }
}
// </vc-code>
