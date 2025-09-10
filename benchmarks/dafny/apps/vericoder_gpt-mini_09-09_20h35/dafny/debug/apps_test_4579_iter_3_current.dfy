function DistinctStrings(strings: seq<string>): set<string>
{
    set i | 0 <= i < |strings| :: strings[i]
}

predicate ValidInput(strings: seq<string>)
{
    |strings| >= 1
}

// <vc-helpers>
lemma DistinctPrefixLeq(strings: seq<string>, k: int)
  requires 0 <= k <= |strings|
  ensures |DistinctStrings(strings[..k])| <= k
{
  if k == 0 {
    assert DistinctStrings(strings[..k]) == {};
    assert |DistinctStrings(strings[..k])| == 0;
  } else {
    DistinctPrefixLeq(strings, k-1);
    var prev := DistinctStrings(strings[..k-1]);
    var s := strings[k-1];
    if s in prev {
      // If s already in previous distinct set, the distinct set for length k is same as prev
      assert DistinctStrings(strings[..k]) == prev;
      assert |DistinctStrings(strings[..k])| == |prev|;
      assert |prev| <= k-1;
      assert |DistinctStrings(strings[..k])| <= k;
    } else {
      // Otherwise, the distinct set for length k is prev plus the new element s
      assert DistinctStrings(strings[..k]) == prev + {s};
      assert |DistinctStrings(strings[..k])| == |prev| + 1;
      assert |prev| <= k-1;
      assert |DistinctStrings(strings[..k])| <= k;
    }
  }
}

lemma DistinctPrefixNonEmpty(strings: seq<string>, k: int)
  requires 0 < k <= |strings|
  ensures |DistinctStrings(strings[..k])| >= 1
{
  // index 0 is within range 0..k-1, so strings[0] is in the distinct set of the prefix
  assert 0 < k;
  assert strings[0] in DistinctStrings(strings[..k]);
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
  var i := 0;
  var seen: set<string> := {};
  var c := 0;
  while i < |strings|
    invariant 0 <= i <= |strings|
    invariant seen == DistinctStrings(strings[..i])
    invariant c == |seen|
    invariant c <= i
  {
    seen := DistinctStrings(strings[..i+1]);
    c := |seen|;
    DistinctPrefixLeq(strings, i+1);
    i := i + 1;
  }
  count := c;
  DistinctPrefixNonEmpty(strings, |strings|);
  DistinctPrefixLeq(strings, |strings|);
}
// </vc-code>

