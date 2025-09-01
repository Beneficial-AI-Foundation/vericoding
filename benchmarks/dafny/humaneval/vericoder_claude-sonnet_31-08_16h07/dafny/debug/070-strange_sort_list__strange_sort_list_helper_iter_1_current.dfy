

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
    
    var i := 0;
    while i < |sorted|
        invariant 0 <= i <= |sorted|
    {
        if i % 2 == 0 {
            assert strange[i] == sorted[i / 2];
        } else {
            assert strange[i] == sorted[|sorted| - (i - 1) / 2 - 1];
        }
        i := i + 1;
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
        return;
    }
    
    strange := [];
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |strange| == i
        invariant forall j :: 0 <= j < i && j % 2 == 0 ==> strange[j] == sorted[j / 2]
        invariant forall j :: 0 <= j < i && j % 2 == 1 ==> strange[j] == sorted[|s| - (j - 1) / 2 - 1]
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
    
    strange_construction_preserves_multiset(sorted, strange);
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