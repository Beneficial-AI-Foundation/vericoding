// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }

function insert(x: int, l: array<int>): array<int>
    requires l != null
    ensures insert(x, l).Length == l.Length + 1
    ensures multiset(insert(x, l)) == multiset(l) + multiset([x])
    ensures forall i, j :: 0 <= i < j < insert(x, l).Length ==> insert(x, l)[i] <= insert(x, l)[j]
{
    if l.Length == 0 then
        [x]
    else if x <= l[0] then
        var r := new int[l.Length + 1];
        r[0] := x;
        forall k | 0 <= k < l.Length { r[k + 1] := l[k]; }
        r
    else
        var r := new int[l.Length + 1];
        r[0] := l[0];
        var rest := insert(x, l[1..]);
        forall k | 0 <= k < rest.Length { r[k + 1] := rest[k]; }
        r
}
// </vc-helpers>

// <vc-spec>
method insertion_sort(l: array<int>) returns (result: array<int>)
    ensures
        /* The result is sorted in non-decreasing order */
        forall i, j :: 0 <= i < j < result.Length ==> result[i] <= result[j]
    ensures
        /* The result is a permutation of the input */
        result.Length == l.Length && multiset(result[..]) == multiset(l[..])
// </vc-spec>
// <vc-code>
{
    if l.Length == 0 {
        result := new int[0];
    } else {
        var sorted := insert(l[0], new int[0]);
        for i := 1 to l.Length
            invariant sorted.Length == i
            invariant multiset(sorted) == multiset(l[0..i])
            invariant forall j, k :: 0 <= j < k < sorted.Length ==> sorted[j] <= sorted[k]
        {
            sorted := insert(l[i], sorted);
        }
        result := sorted;
    }
}
// </vc-code>
