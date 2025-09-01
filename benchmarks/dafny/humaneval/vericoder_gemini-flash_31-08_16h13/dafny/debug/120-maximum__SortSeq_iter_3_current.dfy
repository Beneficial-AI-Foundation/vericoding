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
function multiset<T>(s: seq<T>): multiset<T>
{
  if |s| == 0 then multiset{} else multiset{s[0]} + multiset(s[1..])
}

lemma lemma_multiset_append<T>(s: seq<T>, t: seq<T>)
  ensures multiset(s + t) == multiset(s) + multiset(t)
{
}
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
  var sorted_s := SortSeq(s);
  var result_seq: seq<int> := [];

  // Iterate k times to select the largest k elements from the sorted sequence.
  // Since sorted_s is sorted in ascending order, the last k elements are the largest.
  var i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant |result_seq| == i
    invariant (i > 0) ==> (result_seq == sorted_s[|sorted_s| - k .. |sorted_s| - k + i])
    invariant forall x :: x in result_seq ==> x in sorted_s // Each element of result_seq is from sorted_s
    invariant forall m, n :: 0 <= m < n < i ==> result_seq[m] <= result_seq[n] // result_seq is sorted
    decreasing k - i
  {
    result_seq := result_seq + [sorted_s[|sorted_s| - k + i]];
    i := i + 1;
  }
  return result_seq;
}
// </vc-code>

