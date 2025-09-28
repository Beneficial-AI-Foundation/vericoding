// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed reads clause syntax from nothing to {} */
function Mid(low: int, high: int): int 
    requires low <= high
    reads {}
{
    low + (high - low) / 2
}
// </vc-helpers>

// <vc-spec>
method BinarySearch(v: array<int>, k: int) returns (result: int)
    requires forall i, j :: 0 <= i <= j < v.Length ==> v[i] <= v[j]
    requires exists i :: 0 <= i < v.Length && k == v[i]
    ensures 0 <= result < v.Length
    ensures k == v[result]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Binary search implementation */
{
    var low := 0;
    var high := v.Length - 1;
    
    while low <= high
        invariant 0 <= low <= high + 1 <= v.Length
        invariant forall i :: 0 <= i < low ==> v[i] < k
        invariant forall i :: high < i < v.Length ==> v[i] > k
    {
        var mid := Mid(low, high);
        if v[mid] == k {
            return mid;
        } else if v[mid] < k {
            low := mid + 1;
        } else {
            high := mid - 1;
        }
    }
    
    // This line should never be reached because of the precondition that k exists in v
    return 0;
}
// </vc-code>
