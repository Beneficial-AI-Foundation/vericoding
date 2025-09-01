

// <vc-helpers>
lemma multiset_preservation(s: seq<int>, sorted: seq<int>)
    requires multiset(s) == multiset(sorted)
    ensures multiset(s) == multiset(sorted)
{
}

lemma strange_construction_preserves_multiset(sorted: seq<int>, strange: seq<int>)
    requires |sorted| == |strange|
    requires forall i :: 0 <= i < |sorted| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
    requires forall i :: 0 <= i < |sorted| && i % 2 == 1 ==> strange[i] == sorted[|sorted| - (i - 1) / 2 - 1]
    ensures multiset(sorted) == multiset(strange)
{
    if |sorted| == 0 {
        return;
    }
    
    if |sorted| == 1 {
        assert strange[0] == sorted[0];
        return;
    }
    
    // Prove that each element in sorted appears exactly once in strange
    assert forall k :: 0 <= k < (|sorted| + 1) / 2 ==> 
        k * 2 < |sorted| && sorted[k] == strange[k * 2];
    
    assert forall k :: 0 <= k < |sorted| / 2 ==> 
        k * 2 + 1 < |sorted| && sorted[|sorted| - k - 1] == strange[k * 2 + 1];
    
    // Show that every element in sorted appears in strange
    assert forall j :: 0 <= j < |sorted| ==> 
        (exists i :: 0 <= i < |sorted| && strange[i] == sorted[j]);
    
    // Show that every element in strange appears in sorted  
    assert forall i :: 0 <= i < |strange| ==> 
        (exists j :: 0 <= j < |sorted| && sorted[j] == strange[i]);
}

lemma element_in_multiset_property(sorted: seq<int>, strange: seq<int>, j: int)
    requires |sorted| == |strange|
    requires 0 <= j < |sorted|
    requires forall i :: 0 <= i < |sorted| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
    requires forall i :: 0 <= i < |sorted| && i % 2 == 1 ==> strange[i] == sorted[|sorted| - (i - 1) / 2 - 1]
    ensures sorted[j] in multiset(strange)
{
    if j < (|sorted| + 1) / 2 {
        var even_idx := j * 2;
        if even_idx < |sorted| {
            assert even_idx % 2 == 0;
            assert strange[even_idx] == sorted[even_idx / 2];
            assert even_idx / 2 == j;
            assert strange[even_idx] == sorted[j];
        }
    } else {
        var k := |sorted| - j - 1;
        var odd_idx := k * 2 + 1;
        if odd_idx < |sorted| {
            assert odd_idx % 2 == 1;
            assert strange[odd_idx] == sorted[|sorted| - (odd_idx - 1) / 2 - 1];
            assert (odd_idx - 1) / 2 == k;
            assert |sorted| - k - 1 == j;
            assert strange[odd_idx] == sorted[j];
        }
    }
}
// </vc-helpers>

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
    
    if |s| == 0 {
        strange := [];
        multiset_preservation(s, sorted);
        return;
    }
    
    strange := [];
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |strange| == i
        invariant forall j :: 0 <= j < i && j % 2 == 0 ==> strange[j] == sorted[j / 2]
        invariant forall j :: 0 <= j < i && j % 2 == 1 ==> strange[j] == sorted[|s| - (j - 1) / 2 - 1]
        invariant multiset(s) == multiset(sorted)
    {
        if i % 2 == 0 {
            // Even index: take from beginning of sorted
            var idx := i / 2;
            strange := strange + [sorted[idx]];
        } else {
            // Odd index: take from end of sorted
            var idx := |s| - (i - 1) / 2 - 1;
            strange := strange + [sorted[idx]];
        }
        i := i + 1;
    }
    
    assert |sorted| == |strange|;
    assert forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2];
    assert forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1];
    
    // Prove that every element in sorted appears in strange
    forall j | 0 <= j < |sorted|
        ensures sorted[j] in multiset(strange)
    {
        element_in_multiset_property(sorted, strange, j);
    }
    
    strange_construction_preserves_multiset(sorted, strange);
    assert multiset(sorted) == multiset(strange);
    multiset_preservation(s, sorted);
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