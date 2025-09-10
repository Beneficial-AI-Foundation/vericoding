function seq_min(s: seq<int>): int
    requires |s| > 0
    ensures seq_min(s) in s
    ensures forall k :: 0 <= k < |s| ==> seq_min(s) <= s[k]
{
    if |s| == 1 then s[0]
    else if s[0] <= seq_min(s[1..]) then s[0]
    else seq_min(s[1..])
}

predicate ValidInput(arr: seq<int>)
{
    |arr| >= 2 && 
    exists i, j :: 0 <= i < j < |arr| && arr[i] == arr[j] == seq_min(arr)
}

// <vc-helpers>
function min(a: int, b: int): int {
    if a < b then a else b
}
// </vc-helpers>

// <vc-spec>
method solve(arr: seq<int>) returns (result: int)
    requires ValidInput(arr)
    ensures result > 0
    ensures result <= |arr| - 1
    ensures exists i, j :: 0 <= i < j < |arr| && arr[i] == arr[j] == seq_min(arr) && j - i == result
    ensures forall i, j :: 0 <= i < j < |arr| && arr[i] == arr[j] == seq_min(arr) ==> j - i >= result
// </vc-spec>
// <vc-code>
{
    var minVal := seq_min(arr);
    var firstIdx: int := -1;
    var minDiff: int := |arr| + 1; // Initialize with a value larger than any possible difference

    var i := 0;
    while i < |arr|
        invariant 0 <= i <= |arr|
        invariant firstIdx == -1 || (0 <= firstIdx < i && arr[firstIdx] == minVal)
        invariant 1 <= minDiff <= |arr| + 1
        invariant (exists k, l :: 0 <= k < l < i && arr[k] == minVal && arr[l] == minVal) ==> (minDiff <= |arr| - 1)
        invariant forall k_idx, l_idx :: 0 <= k_idx < l_idx < i && arr[k_idx] == minVal && arr[l_idx] == minVal ==> l_idx - k_idx >= minDiff
        invariant (firstIdx != -1 && i - firstIdx > 0 && arr[firstIdx] == minVal) ==> minDiff <= i - firstIdx
    {
        if arr[i] == minVal {
            if firstIdx != -1 {
                minDiff := min(minDiff, i - firstIdx);
            }
            firstIdx := i;
        }
        i := i + 1;
    }
    result := minDiff;
}
// </vc-code>

