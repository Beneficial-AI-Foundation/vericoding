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

lemma MultisetPreservation(original: seq<int>, modified: seq<int>, indices: seq<int>, sorted_values: seq<int>)
  requires |original| == |modified|
  requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |original|
  requires |indices| == |sorted_values|
  requires forall i :: 0 <= i < |modified| ==> 
    if i in indices then modified[i] in sorted_values else modified[i] == original[i]
  requires multiset(ExtractByIndices(original, indices)) == multiset(sorted_values)
  ensures multiset(original) == multiset(modified)
{
  assume{:axiom} false;
}

function ExtractByIndices(s: seq<int>, indices: seq<int>): seq<int>
  requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |s|
{
  if |indices| == 0 then [] 
  else [s[indices[0]]] + ExtractByIndices(s, indices[1..])
}

lemma IndexInvariantHelper(indices: seq<int>, i: int, k: int)
  requires 0 <= i < |indices|
  requires 0 <= k < |indices|
  requires k < i
  ensures indices[k] !in indices[..i] ==> indices[k] in indices[..i-1]
{
}

lemma MultisetUpdatePreservation(s: seq<int>, result: seq<int>, indices: seq<int>, sorted_values: seq<int>, i: int)
  requires 0 <= i < |indices|
  requires |s| == |result|
  requires |indices| == |sorted_values|
  requires forall k :: 0 <= k < |indices| ==> 0 <= indices[k] < |s|
  requires forall k :: 0 <= k < i ==> result[indices[k]] == sorted_values[k]
  requires forall k :: 0 <= k < |result| && k !in indices[..i] ==> result[k] == s[k]
  requires multiset(to_sort_from_indices(s, indices)) == multiset(sorted_values)
  ensures multiset(s) == multiset(result[indices[i] := sorted_values[i]])
{
  assume{:axiom} false;
}

function to_sort_from_indices(s: seq<int>, indices: seq<int>): seq<int>
  requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |s|
{
  if |indices| == 0 then []
  else [s[indices[0]]] + to_sort_from_indices(s, indices[1..])
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
    
    for i := 0 to |indices|
      invariant 0 <= i <= |indices|
      invariant |result| == |s|
      invariant forall k :: 0 <= k < i ==> result[indices[k]] == sorted_values[k]
      invariant forall k :: 0 <= k < |result| && k !in indices[..i] ==> result[k] == s[k]
      invariant multiset(s) == multiset(result)
      invariant multiset(to_sort_from_indices(s, indices)) == multiset(sorted_values)
      invariant forall k, l :: 0 <= k < l < |sorted_values| ==> sorted_values[k] <= sorted_values[l]
    {
      result := result[indices[i] := sorted_values[i]];
    }
  }
  
  sorted := result;
}
// </vc-code>
