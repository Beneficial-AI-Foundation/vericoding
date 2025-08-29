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
{
  assume{:axiom} false;
}

// <vc-helpers>
function extract_predicate_elements(s: seq<int>, p: seq<bool>): seq<int>
  requires |s| == |p|
{
  if |s| == 0 then []
  else if p[0] then [s[0]] + extract_predicate_elements(s[1..], p[1..])
  else extract_predicate_elements(s[1..], p[1..])
}

function get_predicate_indices(p: seq<bool>): seq<int>
{
  if |p| == 0 then []
  else if p[0] then [0] + seq(|get_predicate_indices(p[1..])|, i requires 0 <= i < |get_predicate_indices(p[1..])| => get_predicate_indices(p[1..])[i] + 1)
  else seq(|get_predicate_indices(p[1..])|, i requires 0 <= i < |get_predicate_indices(p[1..])| => get_predicate_indices(p[1..])[i] + 1)
}

method sort_sequence(values: seq<int>) returns (sorted_values: seq<int>)
  ensures |sorted_values| == |values|
  ensures forall i, j :: 0 <= i < j < |sorted_values| ==> sorted_values[i] <= sorted_values[j]
  ensures multiset(values) == multiset(sorted_values)
{
  sorted_values := values;
  var n := |sorted_values|;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |sorted_values| == |values|
    invariant multiset(sorted_values) == multiset(values)
    invariant forall x, y :: 0 <= x < y < i ==> sorted_values[x] <= sorted_values[y]
    invariant forall x, y :: 0 <= x < i <= y < n ==> sorted_values[x] <= sorted_values[y]
  {
    var j := i + 1;
    var min_idx := i;
    while j < n
      invariant i < j <= n
      invariant i <= min_idx < n
      invariant forall k :: i <= k < j ==> sorted_values[min_idx] <= sorted_values[k]
    {
      if sorted_values[j] < sorted_values[min_idx] {
        min_idx := j;
      }
      j := j + 1;
    }
    if min_idx != i {
      var temp := sorted_values[i];
      sorted_values := sorted_values[i := sorted_values[min_idx]][min_idx := temp];
    }
    i := i + 1;
  }
}

function count_pred_up_to(p: seq<bool>, i: int): int
  requires 0 <= i <= |p|
{
  if i == 0 then 0
  else count_pred_up_to(p, i-1) + (if p[i-1] then 1 else 0)
}

lemma count_pred_property(p: seq<bool>, i: int)
  requires 0 <= i < |p|
  ensures count_pred_up_to(p, i+1) == count_pred_up_to(p, i) + (if p[i] then 1 else 0)
{
}

lemma multiset_update_lemma(s: seq<int>, i: int, val: int)
  requires 0 <= i < |s|
  ensures multiset(s[i := val]) == multiset(s) - multiset{s[i]} + multiset{val}
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
Sort elements. Requires: returns the correct size/count. Ensures: returns the correct size/count; the result is sorted according to the ordering relation; returns a sorted permutation of the input; the result is sorted according to the ordering relation.
*/
// </vc-description>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
  if |s| == 0 {
    sorted := s;
    return;
  }
  
  var pred_indices: seq<int> := [];
  var pred_values: seq<int> := [];
  
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |pred_indices| == |pred_values|
    invariant forall k :: 0 <= k < |pred_indices| ==> 0 <= pred_indices[k] < |s| && p[pred_indices[k]]
    invariant forall k :: 0 <= k < |pred_values| ==> pred_values[k] == s[pred_indices[k]]
    invariant forall k :: 0 <= k < |pred_indices| ==> pred_indices[k] < i
    invariant forall k :: 0 <= k < i && p[k] ==> exists idx :: 0 <= idx < |pred_indices| && pred_indices[idx] == k
    invariant |pred_indices| == count_pred_up_to(p, i)
  {
    if p[i] {
      pred_indices := pred_indices + [i];
      pred_values := pred_values + [s[i]];
    }
    count_pred_property(p, i);
    i := i + 1;
  }
  
  var sorted_pred_values := sort_sequence(pred_values);
  
  sorted := s;
  i := 0;
  var pred_idx := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant 0 <= pred_idx <= |pred_indices|
    invariant |sorted| == |s|
    invariant pred_idx == count_pred_up_to(p, i)
    invariant forall k :: 0 <= k < i && !p[k] ==> sorted[k] == s[k]
    invariant forall k :: 0 <= k < i && p[k] ==> 
      exists idx :: 0 <= idx < count_pred_up_to(p, i) && pred_indices[idx] == k && sorted[k] == sorted_pred_values[idx]
    invariant multiset(pred_values) == multiset(sorted_pred_values)
    invariant forall j :: 0 <= j < i ==> (if p[j] then multiset{sorted[j]} <= multiset(sorted_pred_values) else sorted[j] == s[j])
  {
    if p[i] {
      assert pred_idx < |sorted_pred_values|;
      sorted := sorted[i := sorted_pred_values[pred_idx]];
      pred_idx := pred_idx + 1;
    }
    count_pred_property(p, i);
    i := i + 1;
  }
}
// </vc-code>

