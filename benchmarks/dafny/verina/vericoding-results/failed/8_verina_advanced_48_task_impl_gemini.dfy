// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed unresolved identifier 'result' by naming the return value */
function Merge(a: seq<int>, b: seq<int>): (res: seq<int>)
    requires forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
    requires forall i, j :: 0 <= i < j < |b| ==> b[i] <= b[j]
    ensures |res| == |a| + |b|
    ensures multiset(res) == multiset(a) + multiset(b)
    ensures forall i, j :: 0 <= i < j < |res| ==> res[i] <= res[j]
    decreases |a| + |b|
{
    if |a| == 0 then b
    else if |b| == 0 then a
    else if a[0] <= b[0] then
        [a[0]] + Merge(a[1..], b)
    else
        [b[0]] + Merge(a, b[1..])
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
    /* code modified by LLM (iteration 2): no changes, code appears correct once helper is fixed */
    if |list| <= 1 {
        result := list;
    } else {
        var mid := |list| / 2;
        var left := MergeSort(list[..mid]);
        var right := MergeSort(list[mid..]);
        result := Merge(left, right);
    }
}
// </vc-code>
