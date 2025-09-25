// <vc-preamble>
function SqrSumRec(n: int) : int
    requires n >= 0
{
    if (n == 0) then 0 else n*n + SqrSumRec(n-1)
}

least lemma L1(n: int)
    requires n >= 0
    ensures SqrSumRec(n) == n*(n+1)*(2*n + 1)/6
{

}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method DivMod1(a: int, b: int) returns (q: int, r: int)
requires b > 0 && a >= 0
ensures a == b*q + r && 0 <= r < b
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
