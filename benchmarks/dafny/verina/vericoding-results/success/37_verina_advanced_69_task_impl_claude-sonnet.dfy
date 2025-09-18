// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SearchInsert(xs: array<int>, target: int) returns (result: int)
    requires forall i, j :: 0 <= i < j < xs.Length ==> xs[i] < xs[j]
    ensures 0 <= result <= xs.Length
    ensures forall i :: 0 <= i < result ==> xs[i] < target
    ensures result < xs.Length ==> target <= xs[result]
// </vc-spec>
// <vc-code>
{
    var left := 0;
    var right := xs.Length;
    
    while left < right
        invariant 0 <= left <= right <= xs.Length
        invariant forall i :: 0 <= i < left ==> xs[i] < target
        invariant forall i :: right <= i < xs.Length ==> target <= xs[i]
    {
        var mid := (left + right) / 2;
        if xs[mid] < target {
            left := mid + 1;
        } else {
            right := mid;
        }
    }
    
    result := left;
}
// </vc-code>
