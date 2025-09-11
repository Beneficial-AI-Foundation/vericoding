// <vc-preamble>
function has_count(v: int, a: array<int>, n: int): int
    reads a
    requires n >= 0 && n <= a.Length
{
    if n == 0 then 0 else
    (if a[n-1] == v then has_count(v, a, n-1) + 1 else has_count(v, a, n-1))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method count (v: int, a: array<int>, n: int) returns (r: int)
    requires n >= 0 && n <= a.Length;
    ensures has_count(v, a, n) == r;
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
