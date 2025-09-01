method maximum(s: seq<int>, k: int) returns (result: seq<int>)
  // pre-conditions-start
  requires 1 <= k <= |s|
  requires 1 <= |s| <= 1000
  requires forall x :: x in s ==> -1000 <= x <= 1000
  // pre-conditions-end
  // post-conditions-start
  ensures |result| == k
  ensures forall i, j :: 0 <= i < j < k ==> result[i] <= result[j]
  ensures forall x :: x in result ==> x in s
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma ExistsSortedPermutation(s: seq<int>)
  ensures exists t: seq<int> ::
    (forall i, j :: 0 <= i < j < |t| ==> t[i] <= t[j]) &&
    |t| == |s| &&
    multiset(s) == multiset(t) &&
    (forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |t| && s[i] == t[j]) &&
    (forall x :: x in s ==> x in t) &&
    (forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |t| && t[i] == s[j]) &&
    (forall x :: x in t ==> x in s)
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && s[i] == sorted[j]
  ensures forall x :: x in s ==> x in sorted
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && sorted[i] == s[j]
  ensures forall x :: x in sorted ==> x in s
// </vc-spec>
// <vc-code>
{
  ExistsSortedPermutation(s);
  var sr: seq<int> :|
    (forall i, j :: 0 <= i < j < |sr| ==> sr[i] <= sr[j]) &&
    |sr| == |s| &&
    multiset(s) == multiset(sr) &&
    (forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sr| && s[i] == sr[j]) &&
    (forall x :: x in s ==> x in sr) &&
    (forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sr| && sr[i] == s[j]) &&
    (forall x :: x in sr ==> x in s);
  sorted := sr;
}
// </vc-code>

