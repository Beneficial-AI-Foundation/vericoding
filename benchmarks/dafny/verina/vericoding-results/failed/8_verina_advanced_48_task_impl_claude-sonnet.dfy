// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added explicit assertions to prove properties */
function IsSorted(s: seq<int>): bool
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function Merge(left: seq<int>, right: seq<int>): seq<int>
    requires IsSorted(left) && IsSorted(right)
    ensures IsSorted(Merge(left, right))
    ensures multiset(Merge(left, right)) == multiset(left) + multiset(right)
    ensures |Merge(left, right)| == |left| + |right|
    decreases |left| + |right|
{
    if |left| == 0 then right
    else if |right| == 0 then left
    else if left[0] <= right[0] then
        assert IsSorted(left[1..]);
        assert multiset([left[0]]) + multiset(Merge(left[1..], right)) == multiset([left[0]]) + multiset(left[1..]) + multiset(right);
        assert multiset([left[0]]) + multiset(left[1..]) == multiset(left);
        [left[0]] + Merge(left[1..], right)
    else
        assert IsSorted(right[1..]);
        assert multiset([right[0]]) + multiset(Merge(left, right[1..])) == multiset([right[0]]) + multiset(left) + multiset(right[1..]);
        assert multiset([right[0]]) + multiset(right[1..]) == multiset(right);
        [right[0]] + Merge(left, right[1..])
}

function MergeSortFunc(list: seq<int>): seq<int>
    ensures |MergeSortFunc(list)| == |list|
    ensures IsSorted(MergeSortFunc(list))
    ensures multiset(MergeSortFunc(list)) == multiset(list)
    decreases |list|
{
    if |list| <= 1 then list
    else
        var mid := |list| / 2;
        var left := MergeSortFunc(list[0..mid]);
        var right := MergeSortFunc(list[mid..]);
        assert multiset(left) == multiset(list[0..mid]);
        assert multiset(right) == multiset(list[mid..]);
        assert multiset(list[0..mid]) + multiset(list[mid..]) == multiset(list);
        Merge(left, right)
}
// </vc-helpers>

// <vc-spec>
method MergeSort(list: seq<int>) returns (result: seq<int>)
    ensures
        |result| == |list| &&
        (forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]) &&
        multiset(result) == multiset(list)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Simple call to verified MergeSortFunc */
{
    result := MergeSortFunc(list);
}
// </vc-code>
