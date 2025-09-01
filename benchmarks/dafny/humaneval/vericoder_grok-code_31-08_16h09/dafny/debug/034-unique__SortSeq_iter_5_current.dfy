method uniqueSorted(s: seq<int>) returns (result: seq<int>)
    // pre-conditions-start
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    // pre-conditions-end
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}
method unique(s: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

static lemma InsertInSortedMaintainsSorted(s: seq<int>, val: int, pos: int)
  requires 0 <= pos <= |s|
  requires IsSorted(s)
  requires forall a :: 0 <= a < pos ==> s[a] <= val
  requires forall k :: pos <= k < |s| ==> s[k] > val
  ensures IsSorted(s[..pos] + [val] + s[pos..])
{
  var res := s[..pos] + [val] + s[pos..];
  if |res| < 2 { return; }
  forall i, j | 0 <= i < j < |res|
  {
    if j <= pos {
      assert s[j] <= s[i];
    } else if i < pos {
      assert res[i] == s[i] && res[j] == s[j-pos];
      assert s[i] <= val <= s[j-pos];
    } else {
      assert j >= pos+1;
      assert res[i] == val && res[j] == s[j-(pos+1)];
      assert val <= s[j-(pos+1)];
    }
  }
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  sorted := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |sorted| == i
    invariant multiset(sorted) == multiset(s[..i])
    invariant IsSorted(sorted)
  {
    var pos := 0;
    while pos < |sorted| && sorted[pos] <= s[i]
      invariant 0 <= pos <= |sorted|
      invariant forall a :: 0 <= a < pos ==> sorted[a] <= s[i]
    {
      pos := pos + 1;
    }
    assert forall a :: 0 <= a < pos ==> sorted[a] <= s[i];
    if pos < |sorted| {
      assert sorted[pos] > s[i];
      assert forall k :: pos <= k < |sorted| ==> sorted[k] > s[i];
    } else {
      // When pos == |sorted|, the empty suffix has the property vacuously
      assert forall k :: pos <= k < |sorted| ==> sorted[k] > s[i];  // Note: loop doesn't run if false
    }
    InsertInSortedMaintainsSorted(sorted, s[i], pos);
    sorted := sorted[..pos] + [s[i]] + sorted[pos..];
    i := i + 1;
  }
}
// </vc-code>

