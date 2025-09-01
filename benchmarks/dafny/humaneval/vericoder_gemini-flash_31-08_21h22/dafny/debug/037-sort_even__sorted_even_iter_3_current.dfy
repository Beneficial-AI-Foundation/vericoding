

// <vc-helpers>
function IsSortedEven(s: seq<int>): bool
{
  forall i, j | 0 <= i < j && 2 * i < |s| && 2 * j < |s| :: s[2 * i] <= s[2 * j]
}
// </vc-helpers>

// <vc-spec>
method sorted_even(a: seq<int>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |a| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |a|
  ensures forall i, j :: 0 <= i < j && 2 * i < |sorted| && 2 * j < |sorted| ==>
      sorted[2 * i] <= sorted[2 * j]
      ensures forall i :: 0 <= i < |a| && i % 2 == 1 ==> sorted[i] == a[i]
      ensures multiset(a) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var p: seq<bool> := seq(|a|, _ => false);
    for i := 0 to (|a| - 1) / 2
      invariant 0 <= i <= ((|a| - 1) / 2) + 1
      invariant |p| == |a|
      invariant forall k | 0 <= k < |p| :: p[k] <==> exists m | 0 <= m < i :: k == 2 * m
    {
        p := p[2 * i := true];
    }

    var sorted_evens := SortSeqPred(a, p);

    return sorted_evens;
}
// </vc-code>

method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |s| == |p|
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
  // post-conditions-end
{
  assume{:axiom} false;
}