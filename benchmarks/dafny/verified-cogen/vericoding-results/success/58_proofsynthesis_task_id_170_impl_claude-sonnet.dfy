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
lemma SumToAppend(arr: seq<int>, x: int)
    ensures SumTo(arr + [x]) == SumTo(arr) + x
{
    if |arr| == 0 {
        assert arr + [x] == [x];
        assert SumTo([x]) == SumTo([][..0]) + x == 0 + x == x;
        assert SumTo(arr) + x == 0 + x == x;
    } else {
        var arr_prefix := arr[..|arr|-1];
        var last := arr[|arr|-1];
        assert arr == arr_prefix + [last];
        var new_seq := arr + [x];
        assert new_seq == arr_prefix + [last] + [x] == arr_prefix + [last, x];
        assert SumTo(new_seq) == SumTo((arr_prefix + [last, x])[..|arr_prefix + [last, x]|-1]) + (arr_prefix + [last, x])[|arr_prefix + [last, x]|-1];
        assert (arr_prefix + [last, x])[..|arr_prefix + [last, x]|-1] == arr_prefix + [last];
        assert (arr_prefix + [last, x])[|arr_prefix + [last, x]|-1] == x;
        assert SumTo(new_seq) == SumTo(arr_prefix + [last]) + x == SumTo(arr) + x;
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
}
// </vc-code>
