

// <vc-helpers>
lemma StrangeIndexLemma(strange: seq<int>, sorted: seq<int>, min_idx: int, max_idx: int, use_min: bool)
  requires 0 <= min_idx <= max_idx + 1 <= |sorted|
  requires min_idx + (|sorted| - max_idx - 1) == |strange|
  requires use_min ==> |strange| % 2 == 0
  requires !use_min ==> |strange| % 2 == 1
  requires forall i :: 0 <= i < |strange| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
  requires forall i :: 0 <= i < |strange| && i % 2 == 1 ==> strange[i] == sorted[|sorted| - (i - 1) / 2 - 1]
  requires use_min ==> 0 <= min_idx < |sorted|
  requires !use_min ==> 0 <= max_idx < |sorted|
  requires use_min ==> min_idx == |strange| / 2
  requires !use_min ==> max_idx == |sorted| - (|strange| - 1) / 2 - 1
  ensures if use_min then
    (forall i :: 0 <= i < |strange| + 1 && i % 2 == 0 ==> 
      (strange + [sorted[min_idx]])[i] == sorted[i / 2]) &&
    (forall i :: 0 <= i < |strange| + 1 && i % 2 == 1 ==> 
      (strange + [sorted[min_idx]])[i] == sorted[|sorted| - (i - 1) / 2 - 1])
  else
    (forall i :: 0 <= i < |strange| + 1 && i % 2 == 0 ==> 
      (strange + [sorted[max_idx]])[i] == sorted[i / 2]) &&
    (forall i :: 0 <= i < |strange| + 1 && i % 2 == 1 ==> 
      (strange + [sorted[max_idx]])[i] == sorted[|sorted| - (i - 1) / 2 - 1])
{
  var new_strange := if use_min then strange + [sorted[min_idx]] else strange + [sorted[max_idx]];
  
  if use_min {
    assert |strange| % 2 == 0;
    assert new_strange[|strange|] == sorted[min_idx];
    assert min_idx == |strange| / 2;
    assert new_strange[|strange|] == sorted[|strange| / 2];
  } else {
    assert |strange| % 2 == 1;
    assert new_strange[|strange|] == sorted[max_idx];
    assert max_idx == |sorted| - (|strange| - 1) / 2 - 1;
    assert new_strange[|strange|] == sorted[|sorted| - (|strange| - 1) / 2 - 1];
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method strange_sort_list_helper(s: seq<int>) returns (sorted: seq<int>, strange: seq<int>)
Sort elements. Ensures: returns a sorted permutation of the input; returns the correct size/count; the result is sorted according to the ordering relation; the result is sorted according to the ordering relation.
*/
// </vc-description>

// <vc-spec>
method strange_sort_list_helper(s: seq<int>) returns (sorted: seq<int>, strange: seq<int>)
    // post-conditions-start
    ensures multiset(s) == multiset(sorted)
    ensures |s| == |sorted| == |strange|
    ensures forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
    ensures forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1]
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
  sorted := SortSeq(s);
  
  strange := [];
  var min_idx := 0;
  var max_idx := |sorted| - 1;
  var use_min := true;
  
  while |strange| < |s|
    invariant 0 <= min_idx <= max_idx + 1 <= |sorted|
    invariant min_idx + (|sorted| - max_idx - 1) == |strange|
    invariant use_min ==> |strange| % 2 == 0
    invariant !use_min ==> |strange| % 2 == 1
    invariant forall i :: 0 <= i < |strange| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
    invariant forall i :: 0 <= i < |strange| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1]
    invariant use_min ==> min_idx == |strange| / 2
    invariant !use_min ==> max_idx == |s| - (|strange| - 1) / 2 - 1
  {
    StrangeIndexLemma(strange, sorted, min_idx, max_idx, use_min);
    
    if use_min {
      strange := strange + [sorted[min_idx]];
      min_idx := min_idx + 1;
    } else {
      strange := strange + [sorted[max_idx]];
      max_idx := max_idx - 1;
    }
    use_min := !use_min;
  }
}
// </vc-code>

method strange_sort_list(s: seq<int>) returns (strange: seq<int>)
    // post-conditions-start
    ensures |s| == |strange|
    // post-conditions-end
{
  assume{:axiom} false;
}
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}