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
    var minDiff: int := |arr|; // Initialize with a value larger than any possible difference

    var i := 0;
    while i < |arr|
        invariant 0 <= i <= |arr|
        invariant firstIdx == -1 || (0 <= firstIdx < i && arr[firstIdx] == minVal)
        invariant minDiff > 0
        invariant minDiff <= |arr|
        invariant forall k, l :: 0 <= k < l < i && arr[k] == arr[l] == minVal ==> l - k >= minDiff
        invariant (exists k, l :: 0 <= k < l < i && arr[k] == arr[l] == minVal) ==> minDiff < |arr| // if we've found a pair, minDiff must be updated
    {
        if arr[i] == minVal {
            if firstIdx == -1 {
                firstIdx := i;
            } else {
                minDiff := min(minDiff, i - firstIdx);
                // When we find a new minimum, we potentially want to "reset" firstIdx
                // to this current 'i' for future comparisons to find the smallest difference
                // _starting from this new 'i'_
                firstIdx := i; 
            }
        }
        i := i + 1;
    }
    result := minDiff;
}
// </vc-code>

