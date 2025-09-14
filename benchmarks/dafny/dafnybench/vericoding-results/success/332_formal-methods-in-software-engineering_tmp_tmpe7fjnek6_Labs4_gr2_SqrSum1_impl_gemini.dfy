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
lemma L1_induction_helper(n: int)
  requires n > 0
  ensures 6*n*n + (n-1)*n*(2*(n-1)+1) == n*(n+1)*(2*n+1)
{
}
// </vc-helpers>

// <vc-spec>
method SqrSum1(n: int) returns (s: int)
    requires n >= 0
    ensures s == SqrSumRec(n)
// </vc-spec>
// <vc-code>
{
  L1(n);
  s := n * (n + 1) * (2 * n + 1) / 6;
}
// </vc-code>
