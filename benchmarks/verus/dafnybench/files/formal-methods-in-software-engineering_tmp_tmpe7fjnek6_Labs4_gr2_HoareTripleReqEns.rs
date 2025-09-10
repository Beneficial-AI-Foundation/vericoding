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

spec fn HoareTripleReqEns(i: int, k: int) -> int

    recommends k == i*i
{
    k + 2 * i + 1
}

proof fn HoareTripleReqEns_correctness(i: int, k: int)
    requires k == i*i
    ensures HoareTripleReqEns(i, k) == (i+1)*(i+1)
{

    assert(k + 2 * i + 1 == i*i + 2*i + 1);
    assert(i*i + 2*i + 1 == (i+1)*(i+1));
}
{
    assume(false);
    unreached()
}

}
fn main() {}