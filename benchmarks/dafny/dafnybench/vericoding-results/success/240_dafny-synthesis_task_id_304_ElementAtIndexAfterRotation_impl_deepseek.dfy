

// <vc-helpers>
lemma ModLemma(a: int, b: int)
  requires b > 0
  ensures a % b >= 0
{
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
  var m := |l|;
  ModLemma(index - n + m, m);
  element := l[(index - n + m) % m];
}
// </vc-code>

