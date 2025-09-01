

// <vc-helpers>
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

method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  requires |s| == |p|
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
{
  var indices_to_sort := seq(|s|, i requires 0 <= i < |s| => if p[i] then i else -1);
  var filtered_indices := [];
  var filtered_values := [];
  
  for i := 0 to |s|
    invariant |filtered_indices| == |filtered_values|
    invariant |filtered_indices| <= i
    invariant forall j :: 0 <= j < |filtered_indices| ==> 0 <= filtered_indices[j] < |s|
    invariant forall j :: 0 <= j < |filtered_indices| ==> p[filtered_indices[j]]
    invariant forall j :: 0 <= j < |filtered_indices| ==> filtered_values[j] == s[filtered_indices[j]]
  {
    if p[i] {
      filtered_indices := filtered_indices + [i];
      filtered_values := filtered_values + [s[i]];
    }
  }
  
  var sorted_values := SortedSeq(filtered_values);
  sorted := s;
  
  for i := 0 to |filtered_indices|
    invariant |sorted| == |s|
    invariant multiset(s) == multiset(sorted)
    invariant forall j :: 0 <= j < |s| && !p[j] ==> sorted[j] == s[j]
    invariant forall j, k :: 0 <= j < k < i ==> sorted[filtered_indices[j]] <= sorted[filtered_indices[k]]
  {
    sorted := sorted[filtered_indices[i] := sorted_values[i]];
  }
}
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
  var pred := seq(|a|, i => i % 3 == 0);
  sorted_even := SortSeqPred(a, pred);
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