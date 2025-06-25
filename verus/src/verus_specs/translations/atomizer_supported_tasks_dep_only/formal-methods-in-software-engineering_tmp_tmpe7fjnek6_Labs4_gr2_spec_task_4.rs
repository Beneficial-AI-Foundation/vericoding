pub fn HoareTripleReqEns(i: int, k: int) -> (k': int)
    requires(k == i*i)
    ensures(k' == (i+1)*(i+1))
{
}

proof fn L1(n: int)
    requires(n >= 0)
    ensures(SqrSumRec(n) == n*(n+1)*(2*n + 1)/6)
{
}