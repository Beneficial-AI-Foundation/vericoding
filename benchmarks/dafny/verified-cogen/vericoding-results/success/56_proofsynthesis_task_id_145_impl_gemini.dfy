// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
function max(a: int, b: int): int { if a > b then a else b }
// </vc-helpers>

// <vc-spec>
method MaxDifference(arr: array<int>) returns (diff: int)
    requires arr.Length > 0
    requires forall i :: 0 <= i < arr.Length ==> -1073741824 < arr[i] < 1073741823
    ensures forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length ==> arr[i] - arr[j] <= diff
// </vc-spec>
// <vc-code>
{
    assert arr.Length > 0;
    var min_val := arr[0];
    var max_val := arr[0];
    var i := 1;
    while i < arr.Length
        invariant 1 <= i <= arr.Length
        invariant forall j :: 0 <= j < i ==> min_val <= arr[j] <= max_val
        invariant exists j :: 0 <= j < i && arr[j] == min_val
        invariant exists j :: 0 <= j < i && arr[j] == max_val
    {
        min_val := min(min_val, arr[i]);
        max_val := max(max_val, arr[i]);
        i := i + 1;
    }
    diff := max_val - min_val;
}
// </vc-code>
