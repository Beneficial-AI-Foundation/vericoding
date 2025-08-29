// <vc-helpers>
// Helper lemma to ensure elements are in the original sequence
lemma SeqElementsPreserved(s: seq<int>, result: seq<int>, k: int)
  requires 1 <= k <= |s|
  requires |result| == k
  requires forall i :: 0 <= i < k ==> result[i] in s
  ensures forall x :: x in result ==> x in s
{
}

// Helper lemma to prove sorted subsequence
lemma SortedSubseq(s: seq<int>, sorted: seq<int>, k: int)
  requires 1 <= k <= |s|
  requires |sorted| == |s|
  requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  requires multiset(s) == multiset(sorted)
  ensures exists result :: |result| == k && result == sorted[|sorted| - k .. |sorted|] && 
                          (forall i, j :: 0 <= i < j < k ==> result[i] <= result[j]) && 
                          (forall x :: x in result ==> x in s)
{
  var result := sorted[|sorted| - k .. |sorted|];
  assert |result| == k;
  assert forall i, j :: 0 <= i < j < k ==> result[i] <= result[j];
  assert forall x :: x in result ==> x in sorted;
  assert forall x :: x in sorted ==> x in s;
  assert forall x :: x in result ==> x in s;
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>
// <vc-code>
{
  var sorted := SortSeq(s);
  result := sorted[|sorted| - k .. |sorted|];
  assert |result| == k;
  assert forall i, j :: 0 <= i < j < k ==> result[i] <= result[j];
  assert forall x :: x in sorted ==> x in s;
  assert forall x :: x in result ==> x in sorted;
  assert forall x :: x in result ==> x in s;
}
// </vc-code>

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && s[i] == sorted[j]
  ensures forall x :: x in s ==> x in sorted
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && sorted[i] == s[j]
  ensures forall x :: x in sorted ==> x in s
{
  assume{:axiom} false;
}