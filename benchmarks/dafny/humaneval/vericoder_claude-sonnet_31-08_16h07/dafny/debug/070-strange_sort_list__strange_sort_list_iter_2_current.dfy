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
lemma StrangeSortPreservesLength(s: seq<int>, sorted: seq<int>, strange: seq<int>)
    requires |s| == |sorted| == |strange|
    ensures |s| == |strange|
{
}

lemma StrangeSortHelperExists(s: seq<int>)
    ensures exists sorted: seq<int>, strange: seq<int> ::
        multiset(s) == multiset(sorted) &&
        |s| == |sorted| == |strange| &&
        (forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2]) &&
        (forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1])
{
    var sorted, strange := strange_sort_list_helper(s);
    assert multiset(s) == multiset(sorted);
    assert |s| == |sorted| == |strange|;
    assert forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2];
    assert forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1];
}
// </vc-helpers>

// <vc-spec>
method strange_sort_list(s: seq<int>) returns (strange: seq<int>)
    // post-conditions-start
    ensures |s| == |strange|
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var sorted, result := strange_sort_list_helper(s);
    strange := result;
    StrangeSortHelperExists(s);
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