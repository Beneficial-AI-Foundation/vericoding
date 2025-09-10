function DistinctStrings(strings: seq<string>): set<string>
{
    set i | 0 <= i < |strings| :: strings[i]
}

predicate ValidInput(strings: seq<string>)
{
    |strings| >= 1
}

// <vc-helpers>
lemma DistinctBound(t: seq<string>, k: int)
  requires 0 <= k <= |t|
  ensures |DistinctStrings(t[..k])| <= k
{
  if k == 0 {
    assert DistinctStrings(t[..k]) == {};
    assert |DistinctStrings(t[..k])| == 0;
  } else {
    DistinctBound(t, k-1);
    var prev := DistinctStrings(t[..k-1]);
    var s := t[k-1];
    if s in prev {
      // distinct set of prefix of length k equals prev
      assert DistinctStrings(t[..k]) == prev;
      assert |DistinctStrings(t[..k])| == |prev|;
      assert |prev| <= k-1;
      assert |DistinctStrings(t[..k])| <= k;
    } else {
      // distinct set of prefix of length k is prev plus new element
      assert DistinctStrings(t[..k]) == prev + {s};
      assert |DistinctStrings(t[..k])| == |prev| + 1;
      assert |prev| <= k-1;
      assert |DistinctStrings(t[..k])| <= k;
    }
  }
}

lemma DistinctNonEmpty(t: seq<string>, k: int)
  requires 0 < k <= |t|
  ensures |DistinctStrings(t[..k])| >= 1
{
  // The element at index 0 of the prefix is in the distinct set, hence non-empty
  assert 0 < k;
  assert t[0] in DistinctStrings(t[..k]);
  assert DistinctStrings(t[..k]) != {};
  assert |DistinctStrings(t[..k])| >= 1;
}
// </vc-helpers>

// <vc-spec>
method solve(strings: seq<string>) returns (count: int)
    requires ValidInput(strings)
    ensures count >= 1
    ensures count <= |strings|
    ensures count == |DistinctStrings(strings)|
// </vc-spec>
// <vc-code>
{
  DistinctNonEmpty(strings, |strings|);
  DistinctBound(strings, |strings|);
  count := |DistinctStrings(strings)|;
}
// </vc-code>

