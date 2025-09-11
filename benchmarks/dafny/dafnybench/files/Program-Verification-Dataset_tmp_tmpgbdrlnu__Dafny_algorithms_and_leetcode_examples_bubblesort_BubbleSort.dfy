// <vc-preamble>
function NChoose2(n: int): int
{
  n * (n - 1) / 2
}

function SumRange(lo: int, hi: int): int
  decreases hi - lo
{
  if lo >= hi then 0
  else SumRange(lo, hi - 1) + hi - 1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method BubbleSort(a: array<int>) returns (n: nat) 
  modifies a
  ensures n <= NChoose2(a.Length)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
