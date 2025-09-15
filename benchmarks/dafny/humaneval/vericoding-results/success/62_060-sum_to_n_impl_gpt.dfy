// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SumToNFormula(n: int): int { n * (n + 1) / 2 }
// </vc-helpers>

// <vc-spec>
method sum_to_n(n: int) returns (r : int)

  ensures r == n * (n + 1) / 2
// </vc-spec>
// <vc-code>
{
  r := n * (n + 1) / 2;
}
// </vc-code>
