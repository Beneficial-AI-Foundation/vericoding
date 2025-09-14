// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added sorted sequence predicate, MergeSeq, preservation/length lemmas, ArraySortedToSeq, and ArraySliceAppend helper */
predicate SortedSeq(s: seq<int>) { forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j] }

function MergeSeq(s1: seq<int>, s2: seq<int>): seq<int>
  decreases |s1| + |s2|
{
  if |s1| == 0 then s2
  else if |s2| == 0 then s1
  else if s1[0] <= s2[0] then s1[0..1] + MergeSeq(s1[1..], s2)
  else s2[0..1] + MergeSeq(s1, s2[1..])
}

lemma MergeSeqPreservesSortedness(s1: seq<int>, s2: seq<int>)
  requires SortedSeq(s1) && SortedSeq(s2)
  ensures SortedSeq(MergeSeq(s1, s2))
{
  if |s1| == 0 || |s2| == 0 {
  } else if s1[0] <= s2[0] {
    MergeSeqPreservesSortedness(s1[1..], s2);
  } else {
    MergeSeqPreservesSortedness(s1, s2[1..]);
  }
}

lemma MergeSeqLength(s1: seq<int>, s2: seq<int>)
  ensures |MergeSeq(s1, s2)| == |s1| + |s2|
{
  if |s1| == 0 || |s2| == 0 {
  } else if s1[0] <= s2[0] {
    MergeSeqLength(s1[1..], s2);
  } else {
    MergeSeqLength(s1, s2[1..]);
  }
}

lemma ArraySortedToSeq(a: array<int>)
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures SortedSeq(a[..])
{
  assert forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j];
}

lemma ArraySliceAppend(a: array<int>, k: int, s: seq<int>, v: int)
  requires 0 <= k < a.Length
  requires a[..k] == s
  requires a[k] == v
  ensures a[..k+1] == s + [v]
{
  assert a[..k+1] == a[..k] + [a[k]];
  assert a[..k] == s;
  assert a[k] == v;
  assert a[..k+1] == s + [v];
}

// </vc-helpers>

// <vc-spec>
method MergeSortedLists(arr1: array<int>, arr2: array<int>) returns (result: array<int>)
    requires 
        forall i, j :: 0 <= i < j < arr1.Length ==> arr1[i] <= arr1[j]
    requires
        forall i, j :: 0 <= i < j < arr2.Length ==> arr2[i] <= arr2[j]
    ensures
        forall i, j :: 0 <= i < j < result.Length ==> result[i] <= result[j]
    ensures
        result.Length == arr1.Length + arr2.Length
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): compute merged sequence with MergeSeq, assert length equality, copy it element-wise into result while maintaining slice invariant */
  result := new int[arr1.Length + arr2.Length];
  var merged := MergeSeq(arr1[..arr1.Length], arr2[..arr2.Length]);
  MergeSeqLength(arr1[..arr1.Length], arr2[..arr2.Length]);
  assert |merged| == arr1.Length + arr2.Length;
  assert |merged| == result.Length;
  var k := 0;
  while k < result.Length
    invariant 0 <= k <= result.Length
    invariant result[..k] == merged[..k]
  {
    result[k] := merged[k];
    ArraySliceAppend(result, k, merged[..k], merged[k]);
    k := k + 1;
  }
  assert result[..result.Length] == merged;
  ArraySortedToSeq(arr1);
  ArraySortedToSeq(arr2);
  MergeSeqPreservesSortedness(arr1[..arr1.Length], arr2[..arr2.Length]);
  assert forall i, j :: 0 <= i < j < result.Length ==> result[i] <= result[j];
}

// </vc-code>
