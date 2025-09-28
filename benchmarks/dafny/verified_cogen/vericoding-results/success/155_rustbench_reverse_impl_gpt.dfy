// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
predicate IsValidIndex(n: int, i: int) { 0 <= i < n }
function RevIndex(n: int, i: int): int
  requires 0 <= i < n
  ensures 0 <= RevIndex(n, i) < n
{ n - 1 - i }
// </vc-helpers>

// <vc-spec>
method reverse(a: array<int>) returns (result: seq<int>)
    ensures
        |result| == a.Length &&
        forall i :: 0 <= i < |result| ==> result[i] == a[a.Length - 1 - i]
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  result := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == a[n - 1 - j]
    decreases n - i
  {
    result := result + [a[n - 1 - i]];
    i := i + 1;
  }
}
// </vc-code>
