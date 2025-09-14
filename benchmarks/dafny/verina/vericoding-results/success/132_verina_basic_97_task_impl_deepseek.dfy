// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

  function min(a: int, b: int): int { if a < b then a else b }
  function max(a: int, b: int): int { if a > b then a else b }
  predicate InRange(x: int, lower: int, upper: int) { lower <= x < upper }

// </vc-helpers>

// <vc-spec>
method TestArrayElements(a: seq<int>, j: nat) returns (result: seq<int>)
    requires j < |a|
    ensures |result| == |a|
    ensures result[j] == 60
    ensures forall k :: 0 <= k < |a| && k != j ==> result[k] == a[k]
// </vc-spec>
// <vc-code>
{
  result := a;
  result := result[..j] + [60] + result[j + 1..];
}
// </vc-code>
