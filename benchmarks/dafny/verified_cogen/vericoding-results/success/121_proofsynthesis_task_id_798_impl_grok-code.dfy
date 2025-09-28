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

// </vc-helpers>

// <vc-spec>
method Sum(arr: array<int>) returns (sum: int)
    ensures SumTo(arr[..]) == sum
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): use SumTo function directly */
  sum := SumTo(arr[..]);
}
// </vc-code>
