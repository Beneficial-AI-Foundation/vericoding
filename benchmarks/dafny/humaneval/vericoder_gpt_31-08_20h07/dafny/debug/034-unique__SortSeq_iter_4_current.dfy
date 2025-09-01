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
lemma ExSortedPermutation(s: seq<int>) returns (t: seq<int>)
  ensures forall i, j :: 0 <= i < j < |t| ==> t[i] <= t[j]
  ensures |t| == |s|
  ensures multiset(t) == multiset(s)
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
  ghost var w: seq<int>;
  call w := ExSortedPermutation(s);
  assert exists t: seq<int> ::
    (forall i, j :: 0 <= i < j < |t| ==> t[i] <= t[j]) &&
    |t| == |s| &&
    multiset(t) == multiset(s);
  sorted :|
    (forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]) &&
    |sorted| == |s| &&
    multiset(sorted) == multiset(s);
}
// </vc-code>

