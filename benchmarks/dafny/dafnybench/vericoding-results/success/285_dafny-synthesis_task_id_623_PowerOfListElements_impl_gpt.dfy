function Power(base: int, exponent: int): int
    requires exponent >= 0
{
    if exponent == 0 then 1
    else base * Power(base, exponent-1)
}

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
method PowerOfListElements(l: seq<int>, n: int) returns (result: seq<int>)
    requires n >= 0
    ensures |result| == |l|
    ensures forall i :: 0 <= i < |l| ==> result[i] == Power(l[i], n)
// </vc-spec>
// <vc-code>
{
  var s: seq<int> := [];
  var i: int := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant |s| == i
    invariant forall j :: 0 <= j < i ==> s[j] == Power(l[j], n)
    decreases |l| - i
  {
    s := s + [Power(l[i], n)];
    i := i + 1;
  }
  return s;
}
// </vc-code>

