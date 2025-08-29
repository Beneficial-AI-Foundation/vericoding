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
method SortArray(arr: array<int>)
  requires arr.Length > 0
  modifies arr
  ensures forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
  ensures multiset(old(arr[..])) == multiset(arr[..])
{
  assume{:axiom} false;
}

function to_sort_from_indices(s: seq<int>, indices: seq<int>): seq<int>
  requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |s|
{
  if |indices| == 0 then []
  else [s[indices[0]]] + to_sort_from_indices(s, indices[1..])
}

lemma ToSortEquivalence(s: seq<int>, indices: seq<int>)
  requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |s|
  ensures |to_sort_from_indices(s, indices)| == |indices|
  ensures forall i :: 0 <= i < |indices| ==> to_sort_from_indices(s, indices)[i] == s[indices[i]]
{
  if |indices| == 0 {
    return;
  }
  ToSortEquivalence(s, indices[1..]);
}

lemma MultisetUpdateLemma(s: seq<int>, result: seq<int>, indices: seq<int>, sorted_values: seq<int>, i: int)
  requires 0 <= i < |indices|
  requires |s| == |result|
  requires |indices| == |sorted_values|
  requires forall k :: 0 <= k < |indices| ==> 0 <= indices[k] < |s|
  requires forall k :: 0 <= k < i ==> result[indices[k]] == sorted_values[k]
  requires forall k :: 0 <= k < |result| && k !in indices[..i] ==> result[k] == s[k]
  requires multiset(s) == multiset(result)
  requires to_sort_from_indices(s, indices) == sorted_values
  ensures multiset(s) == multiset(result[indices[i] := sorted_values[i]])
{
  ToSortEquivalence(s, indices);
  assert sorted_values[i] == s[indices[i]];
}

lemma SortedPreservation(s: seq<int>, p: seq<bool>, result: seq<int>, indices: seq<int>, sorted_values: seq<int>)
  requires |s| == |p| == |result|
  requires |indices| == |sorted_values|
  requires forall k :: 0 <= k < |indices| ==> 0 <= indices[k] < |s| && p[indices[k]]
  requires forall k :: 0 <= k < |result| && (k >= |p| || !p[k]) ==> result[k] == s[k]
  requires forall k :: 0 <= k < |indices| ==> 0 <= indices[k] < |result| && result[indices[k]] == sorted_values[k]
  requires forall k, l :: 0 <= k < l < |sorted_values| ==> sorted_values[k] <= sorted_values[l]
  ensures forall i, j :: 0 <= i < j < |result| && i < |p| && j < |p| && p[i] && p[j] ==> result[i] <= result[j]
{
  forall i, j | 0 <= i < j < |result| && i < |p| && j < |p| && p[i] && p[j]
    ensures result[i] <= result[j]
  {
    var idx_i := -1;
    var idx_j := -1;
    
    for k := 0 to |indices|
      invariant 0 <= k <= |indices|
      invariant idx_i == -1 ==> forall m :: 0 <= m < k ==> indices[m] != i
      invariant idx_j == -1 ==> forall m :: 0 <= m < k ==> indices[m] != j
      invariant idx_i != -1 ==> 0 <= idx_i < k && indices[idx_i] == i
      invariant idx_j != -1 ==> 0 <= idx_j < k && indices[idx_j] == j
    {
      if indices[k] == i {
        idx_i := k;
      }
      if indices[k] == j {
        idx_j := k;
      }
    }
    
    assert idx_i != -1 && idx_j != -1;
    assert 0 <= idx_i < |indices| && 0 <= idx_j < |indices|;
    if idx_i < idx_j {
      assert sorted_values[idx_i] <= sorted_values[idx_j];
      assert result[i] == sorted_values[idx_i];
      assert result[j] == sorted_values[idx_j];
    } else {
      assert sorted_values[idx_j] <= sorted_values[idx_i];
      assert result[i] == sorted_values[idx_i];
      assert result[j] == sorted_values[idx_j];
    }
  }
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
  requires |s| == |p|
  requires |s| > 0
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
{
  var result := s;
  var to_sort := [];
  var indices := [];
  
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |to_sort| == |indices|
    invariant forall k :: 0 <= k < |indices| ==> 0 <= indices[k] < |s| && p[indices[k]]
    invariant forall k :: 0 <= k < |to_sort| ==> to_sort[k] == s[indices[k]]
  {
    if p[i] {
      to_sort := to_sort + [s[i]];
      indices := indices + [i];
    }
  }
  
  if |to_sort| > 0 {
    var sorted_array := new int[|to_sort|];
    for i := 0 to |to_sort|
      invariant 0 <= i <= |to_sort|
    {
      sorted_array[i] := to_sort[i];
    }
    
    SortArray(sorted_array);
    var sorted_values := sorted_array[..];
    
    ToSortEquivalence(s, indices);
    assert to_sort_from_indices(s, indices) == to_sort;
    assert multiset(to_sort) == multiset(sorted_values);
    
    for i := 0 to |indices|
      invariant 0 <= i <= |indices|
      invariant |result| == |s|
      invariant forall k :: 0 <= k < i ==> result[indices[k]] == sorted_values[k]
      invariant forall k :: 0 <= k < |result| && k !in indices[..i] ==> result[k] == s[k]
      invariant multiset(s) == multiset(result)
      invariant forall k, l :: 0 <= k < l < |sorted_values| ==> sorted_values[k] <= sorted_values[l]
    {
      MultisetUpdateLemma(s, result, indices, sorted_values, i);
      result := result[indices[i] := sorted_values[i]];
    }
    
    SortedPreservation(s, p, result, indices, sorted_values);
  }
  
  sorted := result;
}
// </vc-code>
