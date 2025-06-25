pub fn HoareTripleAssmAssrt()
{
}

proof fn L1(n: int)
    requires n >= 0
    ensures SqrSumRec(n) == n*(n+1)*(2*n + 1)/6
{
}