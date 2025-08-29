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
  
  // Prove that sorted and strange contain the same elements by showing bijection
  assert multiset(sorted) == multiset(strange) by {
    // Every element from sorted appears in strange
    forall i | 0 <= i < |sorted|
      ensures sorted[i] in multiset(strange)
    {
      if i < (|s| + 1) / 2 {
        // This element goes to even position 2*i
        var pos := 2 * i;
        if pos < |s| {
          assert strange[pos] == sorted[i];
        }
      } else {
        // This element goes to odd position from the back
        var back_idx := |s| - 1 - i;
        var pos := 2 * back_idx + 1;
        if pos < |s| {
          assert strange[pos] == sorted[|s| - (pos - 1) / 2 - 1];
          assert |s| - (pos - 1) / 2 - 1 == |s| - back_idx - 1 == i;
          assert strange[pos] == sorted[i];
        }
      }
    }
    
    // Every element from strange appears in sorted
    forall i | 0 <= i < |strange|
      ensures strange[i] in multiset(sorted)
    {
      if i % 2 == 0 {
        var sorted_idx := i / 2;
        assert sorted_idx < |sorted|;
        assert strange[i] == sorted[sorted_idx];
      } else {
        var sorted_idx := |s| - (i - 1) / 2 - 1;
        assert 0 <= sorted_idx < |sorted|;
        assert strange[i] == sorted[sorted_idx];
      }
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