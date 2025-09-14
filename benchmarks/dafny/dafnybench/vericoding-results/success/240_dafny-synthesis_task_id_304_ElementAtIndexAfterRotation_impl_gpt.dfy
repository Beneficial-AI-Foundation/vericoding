

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int) returns (element: int)
    requires n >= 0
    requires 0 <= index < |l|
    ensures element == l[(index - n + |l|) % |l|]
// </vc-spec>
// <vc-code>
{
  assert |l| > 0;
  element := l[(index - n + |l|) % |l|];
}
// </vc-code>

