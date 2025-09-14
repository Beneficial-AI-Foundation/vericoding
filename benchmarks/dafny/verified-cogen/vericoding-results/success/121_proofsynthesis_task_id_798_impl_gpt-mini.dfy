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
function Min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method Sum(arr: array<int>) returns (sum: int)
    ensures SumTo(arr[..]) == sum
// </vc-spec>
// <vc-code>
{
  sum := SumTo(arr[..]);
}
// </vc-code>
