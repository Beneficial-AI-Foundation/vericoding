// <vc-helpers>
lemma SeqContainsAllBelow(s: seq<int>, v: int)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  requires forall i :: 0 <= i < |s| ==> s[i] >= 0
  requires 0 <= v <= |s|
  requires forall k :: 0 <= k < v ==> k in s
  ensures forall k :: 0 <= k < v ==> exists i :: 0 <= i < |s| && s[i] == k
{
  var i := 0;
  while i < v
    invariant 0 <= i <= v
    invariant forall k :: 0 <= k < i ==> exists j :: 0 <= j < |s| && s[j] == k
  {
    assert i in s;
    assert exists j :: 0 <= j < |s| && s[j] == i;
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method SmallestMissingNumber(s: seq<int>) returns (v: int)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    ensures 0 <= v
    ensures v !in s
    ensures forall k :: 0 <= k < v ==> k in s
// </vc-spec>
// </vc-spec>

// <vc-code>
method FindSmallestMissingNumber(s: seq<int>) returns (v: int)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  requires forall i :: 0 <= i < |s| ==> s[i] >= 0
  ensures 0 <= v
  ensures v !in s
  ensures forall k :: 0 <= k < v ==> k in s
{
  v := 0;
  while v < |s| && s[v] == v
    invariant 0 <= v <= |s|
    invariant forall k :: 0 <= k < v ==> k in s
  {
    v := v + 1;
  }
  if v < |s| {
    var i := v;
    while i < |s|
      invariant v <= i <= |s|
      invariant forall k :: v <= k < i ==> s[k] >= s[v] > v
    {
      assert s[i] >= s[v] > v;
      i := i + 1;
    }
    assert forall k :: v <= k < |s| ==> s[k] > v;
    var j := 0;
    while j < |s|
      invariant 0 <= j <= |s|
      invariant forall k :: v <= k < j ==> s[k] > v
    {
      if j == v {
        assert s[j] > v;
      } else if j > v {
        assert s[j] >= s[v] > v;
      }
      j := j + 1;
    }
    assert forall k :: v <= k < |s| ==> s[k] > v;
    assert v !in s;
  }
  SeqContainsAllBelow(s, v);
}
// </vc-code>
