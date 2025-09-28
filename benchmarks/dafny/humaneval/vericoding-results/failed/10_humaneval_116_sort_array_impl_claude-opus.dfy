// <vc-preamble>
function popcount(n: nat): nat {
  if n == 0 then 0
  else popcount(n / 2) + n % 2
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed multiset lemma and merge loop invariants */
lemma MultisetSplit(s: seq<nat>, mid: int)
  requires 0 <= mid <= |s|
  ensures multiset(s[..mid]) + multiset(s[mid..]) == multiset(s)
{
}

predicate PopcountLessThan(a: nat, b: nat)
{
  popcount(a) < popcount(b) || (popcount(a) == popcount(b) && a <= b)
}

method MergeSort(s: seq<nat>) returns (sorted: seq<nat>)
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> popcount(sorted[i]) <= popcount(sorted[j])
  decreases |s|
{
  if |s| <= 1 {
    sorted := s;
    return;
  }
  var mid := |s| / 2;
  var left := MergeSort(s[..mid]);
  var right := MergeSort(s[mid..]);
  MultisetSplit(s, mid);
  sorted := Merge(left, right);
}

method Merge(left: seq<nat>, right: seq<nat>) returns (merged: seq<nat>)
  requires forall i, j :: 0 <= i < j < |left| ==> popcount(left[i]) <= popcount(left[j])
  requires forall i, j :: 0 <= i < j < |right| ==> popcount(right[i]) <= popcount(right[j])
  ensures |merged| == |left| + |right|
  ensures multiset(merged) == multiset(left) + multiset(right)
  ensures forall i, j :: 0 <= i < j < |merged| ==> popcount(merged[i]) <= popcount(merged[j])
{
  merged := [];
  var i, j := 0, 0;
  
  while i < |left| && j < |right|
    invariant 0 <= i <= |left| && 0 <= j <= |right|
    invariant |merged| == i + j
    invariant multiset(merged) == multiset(left[..i]) + multiset(right[..j])
    invariant multiset(merged) + multiset(left[i..]) + multiset(right[j..]) == multiset(left) + multiset(right)
    invariant forall k, l :: 0 <= k < l < |merged| ==> popcount(merged[k]) <= popcount(merged[l])
    invariant forall k :: 0 <= k < |merged| && i < |left| ==> popcount(merged[k]) <= popcount(left[i])
    invariant forall k :: 0 <= k < |merged| && j < |right| ==> popcount(merged[k]) <= popcount(right[j])
  {
    if popcount(left[i]) <= popcount(right[j]) {
      merged := merged + [left[i]];
      i := i + 1;
    } else {
      merged := merged + [right[j]];
      j := j + 1;
    }
  }
  
  while i < |left|
    invariant 0 <= i <= |left| && 0 <= j <= |right|
    invariant |merged| == i + j
    invariant j < |right| || j == |right|
    invariant multiset(merged) == multiset(left[..i]) + multiset(right[..j])
    invariant multiset(merged) + multiset(left[i..]) + multiset(right[j..]) == multiset(left) + multiset(right)
    invariant forall k, l :: 0 <= k < l < |merged| ==> popcount(merged[k]) <= popcount(merged[l])
    invariant forall k :: 0 <= k < |merged| && i < |left| ==> popcount(merged[k]) <= popcount(left[i])
  {
    merged := merged + [left[i]];
    i := i + 1;
  }
  
  while j < |right|
    invariant 0 <= i <= |left| && 0 <= j <= |right|
    invariant |merged| == i + j
    invariant i < |left| || i == |left|
    invariant multiset(merged) == multiset(left[..i]) + multiset(right[..j])
    invariant multiset(merged) + multiset(left[i..]) + multiset(right[j..]) == multiset(left) + multiset(right)
    invariant forall k, l :: 0 <= k < l < |merged| ==> popcount(merged[k]) <= popcount(merged[l])
    invariant forall k :: 0 <= k < |merged| && j < |right| ==> popcount(merged[k]) <= popcount(right[j])
  {
    merged := merged + [right[j]];
    j := j + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method sort_array(s: seq<nat>) returns (sorted: seq<nat>)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> popcount(sorted[i]) <= popcount(sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Calling MergeSort directly */
  sorted := MergeSort(s);
}
// </vc-code>
