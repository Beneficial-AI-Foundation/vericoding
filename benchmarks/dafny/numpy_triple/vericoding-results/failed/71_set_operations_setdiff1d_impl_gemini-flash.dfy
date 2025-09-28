// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed semicolon after `set of s` to fix compilation. Sorted elements immediately after creating the set to ensure `unique_elements_set` provides an iterator over sorted unique elements. */
function SortedUnique(s: seq<int>): seq<int>
{
  var unique_elements_set := set of s;
  var sorted_list_as_seq: seq<int> := [];
  for x in unique_elements_set asc
  {
    sorted_list_as_seq := sorted_list_as_seq + [x];
  }
  return sorted_list_as_seq;
}
// </vc-helpers>

// <vc-spec>
method setdiff1d(ar1: seq<int>, ar2: seq<int>) returns (result: seq<int>)
    // Each element in result is from ar1 and not in ar2
    ensures forall i :: 0 <= i < |result| ==> 
        (exists j :: 0 <= j < |ar1| && result[i] == ar1[j]) &&
        (forall k :: 0 <= k < |ar2| ==> result[i] != ar2[k])
    
    // No duplicates in result
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
    
    // Result is sorted in ascending order
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
    
    // All unique values from ar1 not in ar2 are included in result
    ensures forall val {:trigger val in ar1} :: 
        ((exists i :: 0 <= i < |ar1| && ar1[i] == val) && 
         (forall j :: 0 <= j < |ar2| ==> ar2[j] != val)) ==>
        (exists k :: 0 <= k < |result| && result[k] == val)
    
    // Completeness: result contains exactly the values that should be there
    ensures forall val :: 
        (val in result) <==> 
        (val in ar1 && val !in ar2)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Modified logic to correctly populate `temp_result` and `seen_elements_in_ar1`. The loop invariant `temp_result == SortedUnique(...)` was incorrect and removed, as `temp_result` is not necessarily sorted or unique until the final `SortedUnique` call. The main loop now collects elements that are in `ar1` but not `ar2` and have not been seen before, adding them to `temp_result`. The `seen_elements_in_ar1` set tracks all elements from `ar1` processed so far to avoid duplicates. */
{
  var temp_result: seq<int> := [];
  var seen_elements_in_ar1: set<int> := {};
  var ar2_set := set of ar2;

  for i := 0 to |ar1| - 1
    invariant 0 <= i <= |ar1|
    invariant forall x :: x in temp_result ==> x in ar1
    invariant forall x :: x in temp_result ==> (forall k :: 0 <= k < |ar2| ==> x != ar2[k])
  {
    var val := ar1[i];

    if !(val in seen_elements_in_ar1) {
      if !(val in ar2_set) {
        temp_result := temp_result + [val];
      }
      seen_elements_in_ar1 := seen_elements_in_ar1 + {val};
    }
  }

  result := SortedUnique(temp_result);
}
// </vc-code>
