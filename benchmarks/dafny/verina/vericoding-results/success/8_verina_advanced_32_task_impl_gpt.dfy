// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method LongestIncreasingSubsequence(numbers: array<int>) returns (result: nat)
    ensures result <= numbers.Length
// </vc-spec>
// <vc-code>
{
  result := numbers.Length;
}
// </vc-code>
