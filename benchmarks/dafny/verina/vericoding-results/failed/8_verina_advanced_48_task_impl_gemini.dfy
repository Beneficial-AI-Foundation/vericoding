// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Merge(a: seq<int>, b: seq<int>): seq<int>
    requires forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
    requires forall i, j :: 0 <= i < j < |b| ==> b[i] <= b[j]
    ensures |Merge(a,b)| == |a| + |b|
    ensures multiset(Merge(a,b)) == multiset(a) + multiset(b)
    ensures forall i, j :: 0 <= i < j < |Merge(a,b)| ==> Merge(a,b)[i] <= Merge(a,b)[j]
    decreases |a| + |b|
{
    if a == [] then b
    else if b == [] then a
    else if a[0] <= b[0] then [a[0]] + Merge(a[1..], b)
    else [b[0]] + Merge(a, b[1..])
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
    if |list| <= 1 {
        result := list;
    } else {
        var mid := |list| / 2;
        var left := list[..mid];
        var right := list[mid..];
        var sorted_left := MergeSort(left);
        var sorted_right := MergeSort(right);
        result := Merge(sorted_left, sorted_right);
    }
}
// </vc-code>
