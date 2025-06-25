pub fn SqrSum(n: int) -> (s: int)
{
}

pub fn DivMod(a: int, b: int) -> (q: int, r: int)
{
}

pub fn HoareTripleAssmAssrt()
{
}

pub fn HoareTripleReqEns(i: int, k: int) -> (k_: int)
    requires(k == i*i)
    ensures(k_ == (i+1)*(i+1))
{
}

pub fn Invariant1()
{
}

spec fn SqrSumRec(n: int) -> int
    requires(n >= 0)
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

proof fn L(n: int)
    requires(n >= 0)
    ensures(SqrSumBy6(n) == 6 * SqrSumRec(n))
{
}

pub fn DivMod1(a: int, b: int) -> (q: int, r: int)
    requires(b > 0 && a >= 0)
    ensures(a == b*q + r && 0 <= r < b)
{
}

pub fn Main()
{
}