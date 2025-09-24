// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn SqrSumRec(n: int) -> int
    recommends n >= 0
    decreases n
{
    if n == 0 { 0 } else { n*n + SqrSumRec(n-1) }
}

proof fn L1(n: int)
    requires n >= 0
    ensures SqrSumRec(n) == n*(n+1)*(2*n + 1)/6
    decreases n
{
    if n == 0 {

    } else {
        L1(n-1);

    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn HoareTripleReqEns(i: int, k: int) -> (kprime: int)
    recommends k == i*i
    ensures kprime == (i+1)*(i+1)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}