// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int) returns (element: int)
    requires n >= 0
    requires 0 <= index < |l|
    ensures element == l[(index - n + |l|) % |l|]
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  var adjusted_index := (index - n + |l|) % |l|;
  element := l[adjusted_index];
}
// </vc-code>
