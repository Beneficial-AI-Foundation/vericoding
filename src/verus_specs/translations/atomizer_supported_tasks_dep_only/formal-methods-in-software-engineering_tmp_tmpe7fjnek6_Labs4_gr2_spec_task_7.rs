use vstd::prelude::*;

verus! {

spec fn SqrSumRec(n: int) -> int
    recommends n >= 0
{
    if n == 0 { 0 } else { n*n + SqrSumRec(n-1) }
}

pub fn SqrSum1(n: int) -> (s: int)
    requires(n >= 0)
    ensures(s == SqrSumRec(n))
{
}

proof fn L1(n: int)
    requires(n >= 0)
    ensures(SqrSumRec(n) == n*(n+1)*(2*n + 1)/6)
{
}

}