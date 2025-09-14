

// <vc-helpers>
// no helper lemmas needed
// </vc-helpers>

// <vc-spec>
method ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int) returns (element: int)
    requires n >= 0
    requires 0 <= index < |l|
    ensures element == l[(index - n + |l|) % |l|]
// </vc-spec>
// <vc-code>
{
  var m := |l|;
  assert m > 0;
  element := l[(index - n + m) % m];
  return;
}
// </vc-code>

