// <vc-helpers>
function create_predicate(n: int): seq<bool>
  requires n > 0
  ensures |create_predicate(n)| == n
  ensures forall i :: 0 <= i < n ==> create_predicate(n)[i] == (i % 2 == 0)
{
  if n == 1 then [true]
  else create_predicate(n-1) + [if (n-1) % 2 == 0 then true else false]
}

lemma predicate_even_indices(n: int)
  requires n > 0
  ensures |create_predicate(n)| == n
  ensures forall i :: 0 <= i < n ==> create_predicate(n)[i] == (i % 2 == 0)
{
}

method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  requires |s| == |p|
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
{
  var even_indices: seq<int> := [];
  var even_values: seq<int> := [];
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |even_indices| == |even_values|
    invariant forall k :: 0 <= k < |even_indices| ==> even_indices[k] < i && p[even_indices[k]]
    invariant forall k :: 0 <= k < |even_values| ==> even_values[k] == s[even_indices[k]]
  {
    if p[i] {
      even_indices := even_indices + [i];
      even_values := even_values + [s[i]];
    }
    i := i + 1;
  }
  
  var sorted_even_values := SortSeq(even_values);
  sorted := s;
  i := 0;
  
  while i < |even_indices|
    invariant 0 <= i <= |even_indices|
    invariant |sorted| == |s|
    invariant multiset(sorted[..]) == multiset(s)
    invariant forall k :: 0 <= k < i ==> sorted[even_indices[k]] == sorted_even_values[k]
    invariant forall k :: 0 <= k < |s| && !p[k] ==> sorted[k] == s[k]
    invariant forall k, l :: 0 <= k < l < i ==> sorted_even_values[k] <= sorted_even_values[l]
  {
    sorted := sorted[even_indices[i] := sorted_even_values[i]];
    i := i + 1;
  }
}

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures |sorted| == |s|
  ensures multiset(sorted) == multiset(s)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
{
  if |s| <= 1 {
    return s;
  }
  var mid := |s| / 2;
  var left := SortSeq(s[..mid]);
  var right := SortSeq(s[mid..]);
  sorted := Merge(left, right);
}

method Merge(left: seq<int>, right: seq<int>) returns (merged: seq<int>)
  ensures |merged| == |left| + |right|
  ensures multiset(merged) == multiset(left) + multiset(right)
  ensures forall i, j :: 0 <= i < j < |merged| ==> merged[i] <= merged[j]
{
  merged := [];
  var i := 0;
  var j := 0;
  while i < |left| && j < |right|
    invariant 0 <= i <= |left|
    invariant 0 <= j <= |right|
    invariant |merged| == i + j
    invariant multiset(merged) == multiset(left[..i]) + multiset(right[..j])
    invariant forall k, l :: 0 <= k < l < |merged| ==> merged[k] <= merged[l]
  {
    if left[i] <= right[j] {
      merged := merged + [left[i]];
      i := i + 1;
    } else {
      merged := merged + [right[j]];
      j := j + 1;
    }
  }
  merged := merged + left[i..] + right[j..];
}
// </vc-helpers>

// <vc-spec>
method sorted_even(a: seq<int>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |a| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |a|
  ensures forall i, j :: 0 <= i < j && 2 * i < |sorted| && 2 * j < |sorted| ==>
      sorted[2 * i] <= sorted[2 * j]
      ensures forall i :: 0 <= i < |a| && i % 2 == 1 ==> sorted[i] == a[i]
      ensures multiset(a) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var predicate := create_predicate(|a|);
  predicate_even_indices(|a|);
  sorted := SortSeqPred(a, predicate);
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