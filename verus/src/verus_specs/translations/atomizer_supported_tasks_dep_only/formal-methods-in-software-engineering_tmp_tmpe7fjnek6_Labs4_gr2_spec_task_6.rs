pub fn Invariant1()
{
}

pub fn L1(n: int)
    requires(n >= 0)
    ensures(SqrSumRec(n) == n*(n+1)*(2*n + 1)/6)
{
}