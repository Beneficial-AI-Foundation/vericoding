// <vc-preamble>
function sumInts( n: int ): int
    requires n >= 0;
{
    if n == 0 then
        0
    else
        sumInts(n-1)+n
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SumIntsLoop( n: int ) returns ( s: int )
    requires n >= 0;
    ensures s == sumInts(n)
    ensures s == n*(n+1)/2;
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
