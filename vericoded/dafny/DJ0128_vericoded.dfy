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
  sum := 0;
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant sum == SumTo(arr[..i])
  {
    sum := sum + arr[i];
    assert arr[..i+1] == arr[..i] + [arr[i]];
    i := i + 1;
  }
  assert arr[..] == arr[..arr.Length];
}
// </vc-code>
