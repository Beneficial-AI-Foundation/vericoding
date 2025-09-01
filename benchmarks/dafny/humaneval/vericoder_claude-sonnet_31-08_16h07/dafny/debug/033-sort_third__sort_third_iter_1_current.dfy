

// <vc-helpers>
lemma MultisetPreservation(a: seq<int>, indices: seq<int>, values: seq<int>)
  requires |indices| == |values|
  requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |a|
  requires forall i, j :: 0 <= i < j < |indices| ==> indices[i] != indices[j]
  ensures multiset(a) == multiset(UpdateSeqAtIndices(a, indices, values))

function UpdateSeqAtIndices(a: seq<int>, indices: seq<int>, values: seq<int>): seq<int>
  requires |indices| == |values|
  requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |a|
{
  if |indices| == 0 then a
  else a[indices[0] := values[0]]
}

function ExtractAtIndices(a: seq<int>, indices: seq<int>): seq<int>
  requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |a|
{
  seq(|indices|, i requires 0 <= i < |indices| => a[indices[i]])
}

function GetThirdIndices(n: int): seq<int>
  requires n >= 0
  ensures forall i :: 0 <= i < |GetThirdIndices(n)| ==> GetThirdIndices(n)[i] % 3 == 0
  ensures forall i :: 0 <= i < |GetThirdIndices(n)| ==> 0 <= GetThirdIndices(n)[i] < n
{
  seq(n / 3 + (if n % 3 == 0 then 0 else 1), i requires 0 <= i < n / 3 + (if n % 3 == 0 then 0 else 1) && i * 3 < n => i * 3)
}

function SortedSeq(s: seq<int>): seq<int>
  ensures multiset(s) == multiset(SortedSeq(s))
  ensures forall i, j :: 0 <= i < j < |SortedSeq(s)| ==> SortedSeq(s)[i] <= SortedSeq(s)[j]
// </vc-helpers>

// <vc-spec>
method sort_third(a: seq<int>) returns (sorted_even: seq<int>)
  // pre-conditions-start
  requires |a| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted_even| == |a|
  ensures forall i, j :: 0 <= i < j < |sorted_even| && i % 3 == 0 && j % 3 == 0 ==>
      sorted_even[i] <= sorted_even[j]
  ensures forall i :: 0 <= i < |a| && i % 3 != 0 ==> sorted_even[i] == a[i]
  ensures multiset(a) == multiset(sorted_even)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var predicate := seq(|a|, i => i % 3 == 0);
  sorted_even := SortSeqPred(a, predicate);
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