// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added sequence slice lemmas to prove multiset assertions */
lemma SeqSliceLemma<T>(s: seq<T>)
    requires |s| > 0
    ensures multiset([s[0]]) + multiset(s[1..]) == multiset(s)
{
    assert s == [s[0]] + s[1..];
}

lemma SeqPartitionLemma<T>(s: seq<T>, mid: int)
    requires 0 <= mid <= |s|
    ensures multiset(s[..mid]) + multiset(s[mid..]) == multiset(s)
{
    assert s == s[..mid] + s[mid..];
}

function Merge(left: seq<int>, right: seq<int>): seq<int>
    requires forall i, j :: 0 <= i < j < |left| ==> left[i] <= left[j]
    requires forall i, j :: 0 <= i < j < |right| ==> right[i] <= right[j]
    ensures forall i, j :: 0 <= i < j < |Merge(left, right)| ==> Merge(left, right)[i] <= Merge(left, right)[j]
    ensures multiset(Merge(left, right)) == multiset(left) + multiset(right)
    ensures |Merge(left, right)| == |left| + |right|
    decreases |left| + |right|
{
    if |left| == 0 then right
    else if |right| == 0 then left
    else if left[0] <= right[0] then
        SeqSliceLemma(left);
        [left[0]] + Merge(left[1..], right)
    else
        SeqSliceLemma(right);
        [right[0]] + Merge(left, right[1..])
}

function MergeSortImpl(list: seq<int>): seq<int>
    ensures forall i, j :: 0 <= i < j < |MergeSortImpl(list)| ==> MergeSortImpl(list)[i] <= MergeSortImpl(list)[j]
    ensures multiset(MergeSortImpl(list)) == multiset(list)
    ensures |MergeSortImpl(list)| == |list|
    decreases |list|
{
    if |list| <= 1 then list
    else
        var mid := |list| / 2;
        SeqPartitionLemma(list, mid);
        var left := MergeSortImpl(list[..mid]);
        var right := MergeSortImpl(list[mid..]);
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
{
    /* code modified by LLM (iteration 5): using helper function with proper lemmas */
    result := MergeSortImpl(list);
}
// </vc-code>
