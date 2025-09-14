// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method reverse(a: array<int>) returns (result: seq<int>)
    ensures
        |result| == a.Length &&
        forall i :: 0 <= i < |result| ==> result[i] == a[a.Length - 1 - i]
// </vc-spec>
// <vc-code>
{
  var res: seq<int> := [];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant |res| == i
    invariant forall j :: 0 <= j < |res| ==> res[j] == a[a.Length - 1 - j]
  {
    res := res + [a[a.Length - 1 - i]];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
