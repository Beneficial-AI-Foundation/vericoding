

// <vc-helpers>
function MergedArray(a: array<int>, b: array<int>): seq<int>
    reads a, b
{
    a[..] + b[..]
}

function SortedSeq(s: seq<int>): seq<int>
{
    if |s| <= 1 then s
    else
        var pivot := s[0];
        var smaller := seq(x | x in s && x < pivot, x);
        var equal := seq(x | x in s && x == pivot, x);
        var larger := seq(x | x in s && x > pivot, x);
        SortedSeq(smaller) + equal + SortedSeq(larger)
}
// </vc-helpers>

// <vc-spec>
method FindMedian(a: array<int>, b: array<int>) returns (median: int)
    requires a != null && b != null
    requires a.Length == b.Length
    requires a.Length > 0
    requires forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i + 1]
    requires forall i :: 0 <= i < b.Length - 1 ==> b[i] <= b[i + 1]
    ensures median == if (a.Length % 2 == 0) then (a[a.Length / 2 - 1] + b[0]) / 2 else a[a.Length / 2]
// </vc-spec>
// <vc-code>
{
    var merged := new int[a.Length + b.Length];
    var i, j, k := 0, 0, 0;
    
    // Merge the two sorted arrays
    while i < a.Length && j < b.Length
        invariant 0 <= i <= a.Length
        invariant 0 <= j <= b.Length
        invariant k == i + j
        invariant k <= merged.Length
    {
        if a[i] <= b[j] {
            merged[k] := a[i];
            i := i + 1;
        } else {
            merged[k] := b[j];
            j := j + 1;
        }
        k := k + 1;
    }
    
    // Copy remaining elements from a
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant j == b.Length
        invariant k == i + j
        invariant k <= merged.Length
    {
        merged[k] := a[i];
        i := i + 1;
        k := k + 1;
    }
    
    // Copy remaining elements from b
    while j < b.Length
        invariant i == a.Length
        invariant 0 <= j <= b.Length
        invariant k == i + j
        invariant k <= merged.Length
    {
        merged[k] := b[j];
        j := j + 1;
        k := k + 1;
    }
    
    // Find median
    var totalLength := a.Length + b.Length;
    if totalLength % 2 == 0 {
        median := (merged[totalLength / 2 - 1] + merged[totalLength / 2]) / 2;
    } else {
        median := merged[totalLength / 2];
    }
}
// </vc-code>

