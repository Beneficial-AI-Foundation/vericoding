

// <vc-helpers>
function rotateIndex(index: int, n: int, length: int): int
  requires length > 0
  requires 0 <= index < length
  requires n >= 0
{
  (index - n + length) % length
}
// </vc-helpers>

// <vc-spec>
method ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int) returns (element: int)
    requires n >= 0
    requires 0 <= index < |l|
    ensures element == l[(index - n + |l|) % |l|]
// </vc-spec>
// <vc-code>
{
  element := l[rotateIndex(index, n, |l|)];
}
// </vc-code>

