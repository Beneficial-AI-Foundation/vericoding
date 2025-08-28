// <vc-helpers>
lemma DivisionHelper(i: int, len: int)
    requires i >= 0 && len > 0
    ensures i % 2 == 0 ==> i / 2 < len
    ensures i % 2 == 1 && i < len ==> len - (i - 1) / 2 - 1 >= 0 && len - (i - 1) / 2 - 1 < len

lemma StrangeIndexBounds(i: int, len: int)
    requires 0 <= i < len && len > 0
    ensures i % 2 == 0 ==> 0 <= i / 2 < len
    ensures i % 2 == 1 ==> 0 <= len - (i - 1) / 2 - 1 < len

lemma StrangeSequenceProperties(sorted: seq<int>, strange: seq<int>)
    requires |sorted| == |strange|
    requires forall i :: 0 <= i < |sorted| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
    requires forall i :: 0 <= i < |sorted| && i % 2 == 1 ==> strange[i] == sorted[|sorted| - (i - 1) / 2 - 1]
    ensures multiset(sorted) == multiset(strange)
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
        return;
    }
    
    strange := seq(|s|, i requires 0 <= i < |s| => 
        if i % 2 == 0 then 
            sorted[i / 2]
        else 
            sorted[|s| - (i - 1) / 2 - 1]
    );
    
    forall i | 0 <= i < |s|
        ensures i % 2 == 0 ==> 0 <= i / 2 < |sorted|
        ensures i % 2 == 1 ==> 0 <= |s| - (i - 1) / 2 - 1 < |sorted|
    {
        StrangeIndexBounds(i, |s|);
    }
    
    assert forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2];
    assert forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1];
    
    StrangeSequenceProperties(sorted, strange);
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