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
/* helper modified by LLM (iteration 3): Added lemma to prove SumTo prefix extension property */
lemma SumToExtension(arr: seq<int>, i: int)
    requires 0 <= i < |arr|
    ensures SumTo(arr[..i+1]) == SumTo(arr[..i]) + arr[i]
{
    if i == 0 {
        assert arr[..1] == [arr[0]];
        assert SumTo(arr[..1]) == SumTo([]) + arr[0] == 0 + arr[0] == arr[0];
        assert SumTo(arr[..0]) + arr[0] == 0 + arr[0] == arr[0];
    } else {
        assert arr[..i+1] == arr[..i] + [arr[i]];
        var prefix := arr[..i+1];
        assert prefix == arr[..i] + [arr[i]];
        assert SumTo(prefix) == SumTo(prefix[..|prefix|-1]) + prefix[|prefix|-1];
        assert prefix[..|prefix|-1] == arr[..i];
        assert prefix[|prefix|-1] == arr[i];
    }
}
// </vc-helpers>

// <vc-spec>
method Sum(arr: array<int>) returns (sum: int)
    ensures SumTo(arr[..]) == sum
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed to ensure postcondition holds after loop */
    sum := 0;
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant sum == SumTo(arr[..i])
    {
        SumToExtension(arr[..], i);
        sum := sum + arr[i];
        i := i + 1;
    }
    assert i == arr.Length;
    assert arr[..i] == arr[..];
    assert sum == SumTo(arr[..]);
}
// </vc-code>
