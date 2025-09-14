// <vc-preamble>
function SumTo(arr: seq<int>): int
    decreases |arr|
{
    if |arr| == 0 then
        0
    else
        SumTo(arr[..|arr|-1]) + arr[|arr|-1]
}
// </vc-preamble>

// <vc-helpers>
lemma SumToAppend(s: seq<int>, x: int)
    ensures SumTo(s + [x]) == SumTo(s) + x
{
    if |s| == 0 {
        assert s + [x] == [x];
    } else {
        calc {
            SumTo(s + [x]);
            == SumTo((s + [x])[..|s + [x]| - 1]) + (s + [x])[|s + [x]| - 1];
            == SumTo(s) + x;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method SumRangeList(arr: array<int>, start: int, end: int) returns (sum: int)
    requires 0 <= start <= end
    requires start <= end < arr.Length
    ensures SumTo(arr[start..end+1]) == sum
// </vc-spec>
// <vc-code>
{
    sum := 0;
    var i := start;
    while i <= end
        invariant start <= i <= end + 1
        invariant sum == SumTo(arr[start..i])
    {
        sum := sum + arr[i];
        SumToAppend(arr[start..i], arr[i]);
        assert arr[start..i] + [arr[i]] == arr[start..i+1];
        i := i + 1;
    }
    assert arr[start..i] == arr[start..end+1];
}
// </vc-code>
