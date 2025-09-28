// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added IsSorted predicate, IsSortedTail lemma for subsequences, and fixed merge function with forall in ensures */
predicate IsSorted(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

lemma IsSortedTail(s: seq<int>)
    requires IsSorted(s) && 1 <= |s|
    ensures IsSorted(s[1..])
{
}

function merge(left: seq<int>, right: seq<int>): seq<int>
    requires IsSorted(left) && IsSorted(right)
    ensures (forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j])
    ensures multiset(result) == multiset(left) + multiset(right)
    decreases |left| + |right|
{
    if |left| == 0 then right
    else if |right| == 0 then left
    else if left[0] <= right[0] then
        IsSortedTail(left);
        [left[0]] + merge(left[1..], right)
    else
        IsSortedTail(right);
        [right[0]] + merge(left, right[1..])
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
/* code modified by LLM (iteration 2): recursive implementation of MergeSort calling merge helper */
{
    if |list| <= 1 {
        result := list;
    } else {
        var mid := |list| / 2;
        var left := MergeSort(list[..mid]);
        var right := MergeSort(list[mid..]);
        result := merge(left, right);
    }
}
// </vc-code>
