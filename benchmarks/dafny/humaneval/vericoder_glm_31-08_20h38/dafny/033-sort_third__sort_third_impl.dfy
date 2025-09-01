

// <vc-helpers>
function Insert(x: int, s: seq<int>): seq<int>
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures forall i, j :: 0 <= i < j < |Insert(x, s)| ==> Insert(x, s)[i] <= Insert(x, s)[j]
  ensures multiset(Insert(x, s)) == multiset(s) + multiset([x])
  decreases |s|
{
  if |s| == 0 then [x]
  else if x <= s[0] then [x] + s
  else [s[0]] + Insert(x, s[1..])
}

function SortSeq(s: seq<int>): seq<int>
  ensures forall i, j :: 0 <= i < j < |SortSeq(s)| ==> SortSeq(s)[i] <= SortSeq(s)[j]
  ensures multiset(SortSeq(s)) == multiset(s)
  decreases |s|
{
  if |s| == 0 then []
  else Insert(s[0], SortSeq(s[1..]))
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
  var n := |a|;
  var indices := [i for i in 0..n if i % 3 == 0];
  var values := [a[i] for i in indices];
  var sorted_values := SortSeq(values);
  var result := a;
  for i := 0 to |indices|
    invariant 0 <= i <= |indices|
    invariant forall j :: 0 <= j < |a| && j % 3 != 0 ==> result[j] == a[j]
    invariant multiset(result) == multiset(a) - multiset(values[0..i]) + multiset(sorted_values[0..i])
    invariant forall j :: 0 <= j < i ==> result[indices[j]] == sorted_values[j]
    invariant forall j :: i <= j < |indices| ==> result[indices[j]] == a[indices[j]]
  {
    result[indices[i]] := sorted_values[i];
  }
  return result;
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