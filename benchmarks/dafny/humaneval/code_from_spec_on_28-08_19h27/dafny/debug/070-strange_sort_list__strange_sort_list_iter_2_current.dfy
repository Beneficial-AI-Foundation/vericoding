method strange_sort_list_helper(s: seq<int>) returns (sorted: seq<int>, strange: seq<int>)
    // post-conditions-start
    ensures multiset(s) == multiset(sorted)
    ensures |s| == |sorted| == |strange|
    ensures forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
    ensures forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1]
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma StrangeSortPreservesMultiset(s: seq<int>, sorted: seq<int>, strange: seq<int>)
  requires multiset(s) == multiset(sorted)
  requires |s| == |sorted| == |strange|
  requires forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
  requires forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1]
  ensures multiset(s) == multiset(strange)
{
  if |s| == 0 {
    return;
  }
  
  // Prove that every element in sorted appears in strange
  forall x | x in multiset(sorted)
    ensures x in multiset(strange)
  {
    // Since x is in sorted, there exists some index j such that sorted[j] == x
    var j :| 0 <= j < |sorted| && sorted[j] == x;
    
    // We need to show that x appears in strange
    // There are two cases based on how elements from sorted map to strange:
    // Case 1: Elements from first half of sorted go to even indices in strange
    // Case 2: Elements from second half of sorted go to odd indices in strange
    
    if j < (|s| + 1) / 2 {
      // j maps to even index 2*j in strange (if it exists)
      var strange_idx := 2 * j;
      if strange_idx < |s| {
        assert strange[strange_idx] == sorted[j] == x;
      }
    }
    
    if j >= |s| / 2 {
      // j maps to some odd index in strange
      var strange_idx := 2 * (|s| - j - 1) + 1;
      if strange_idx < |s| {
        assert strange_idx % 2 == 1;
        assert (strange_idx - 1) / 2 == |s| - j - 1;
        assert |s| - (strange_idx - 1) / 2 - 1 == j;
        assert strange[strange_idx] == sorted[j] == x;
      }
    }
  }
  
  // Prove that every element in strange appears in sorted
  forall x | x in multiset(strange)
    ensures x in multiset(sorted)
  {
    var i :| 0 <= i < |strange| && strange[i] == x;
    
    if i % 2 == 0 {
      // Even index: strange[i] == sorted[i / 2]
      assert strange[i] == sorted[i / 2];
      assert x == sorted[i / 2];
    } else {
      // Odd index: strange[i] == sorted[|s| - (i - 1) / 2 - 1]
      var sorted_idx := |s| - (i - 1) / 2 - 1;
      assert strange[i] == sorted[sorted_idx];
      assert x == sorted[sorted_idx];
    }
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method strange_sort_list(s: seq<int>) returns (strange: seq<int>)
Sort elements. Ensures: returns the correct size/count.
*/
// </vc-description>

// <vc-spec>
method strange_sort_list(s: seq<int>) returns (strange: seq<int>)
  ensures |strange| == |s|
  ensures multiset(s) == multiset(strange)
// </vc-spec>
// <vc-code>
{
  var sorted;
  sorted, strange := strange_sort_list_helper(s);
  
  StrangeSortPreservesMultiset(s, sorted, strange);
}
// </vc-code>

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}