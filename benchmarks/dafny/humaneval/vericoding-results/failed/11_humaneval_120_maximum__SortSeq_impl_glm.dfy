// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added assertion to help verifier */
function Insert(sorted: seq<int>, x: int): seq<int>
  requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures forall i, j :: 0 <= i < j < |Insert(sorted, x)| ==> Insert(sorted, x)[i] <= Insert(sorted, x)[j]
  ensures multiset(Insert(sorted, x)) == multiset(sorted) + multiset([x])
  ensures |Insert(sorted, x)| == |sorted| + 1
  decreases |sorted|
{
  if |sorted| == 0 then [x]
  else if x <= sorted[0] then [x] + sorted
  else
    var tail := sorted[1..];
    var newTail := Insert(tail, x);
    assert sorted[0] <= newTail[0];
    [sorted[0]] + newTail
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
  /* code modified by LLM (iteration 2): added assertion to help verifier */
  var result := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |result| == i
    invariant forall k, l :: 0 <= k < l < |result| ==> result[k] <= result[l]
    invariant multiset(result) == multiset(s[0..i])
  {
    result := Insert(result, s[i]);
    assert multiset(result) == multiset(s[0..i+1]);
    i := i + 1;
  }
  return result;
}
// </vc-code>
