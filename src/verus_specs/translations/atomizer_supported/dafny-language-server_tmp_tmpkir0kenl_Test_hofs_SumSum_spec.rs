spec fn Sum(n: nat, f: spec_fn(int) -> int) -> int
{
    if n == 0 { 0 } else { f((n-1) as int) + Sum(n-1, f) }
}

proof fn Exchange(n: nat, f: spec_fn(int) -> int, g: spec_fn(int) -> int)
    requires(forall|i: int| 0 <= i < n ==> f(i) == g(i))
    ensures(Sum(n, f) == Sum(n, g))
{
}

proof fn ExchangeEta(n: nat, f: spec_fn(int) -> int, g: spec_fn(int) -> int)
    requires(forall|i: int| 0 <= i < n ==> f(i) == g(i))
    ensures(Sum(n, |x| f(x)) == Sum(n, |x| g(x)))
{
}

proof fn NestedAlphaRenaming(n: nat, g: spec_fn(int, int) -> int)
    ensures(Sum(n, |x| Sum(n, |y| g(x,y))) == Sum(n, |a| Sum(n, |b| g(a,b))))
{
}

proof fn DistributePlus1(n: nat, f: spec_fn(int) -> int)
    ensures(Sum(n, |x| 1 + f(x)) == n + Sum(n, f))
{
}

proof fn Distribute(n: nat, f: spec_fn(int) -> int, g: spec_fn(int) -> int)
    ensures(Sum(n, |x| f(x) + g(x)) == Sum(n, f) + Sum(n, g))
{
}

proof fn PrettyBasicBetaReduction(n: nat, g: spec_fn(int, int) -> int, i: int)
    ensures((|x| Sum(n, |y| g(x,y)))(i) == Sum(n, |y| g(i,y)))
{
}

proof fn BetaReduction0(n: nat, g: spec_fn(int, int) -> int, i: int)
    ensures((|x| Sum(n, |y| g(x,y)))(i) == Sum(n, |y| g(i,y)))
{
}

proof fn BetaReduction1(n_: nat, g: spec_fn(int, int) -> int, i: int)
    ensures(g(i, n_ as int) + Sum(n_, |y| g(i,y)) == (|x| g(x, n_ as int) + Sum(n_, |y| g(x,y)))(i))
{
}

proof fn BetaReductionInside(n_: nat, g: spec_fn(int, int) -> int)
    ensures(Sum(n_, |x| g(x, n_ as int) + Sum(n_, |y| g(x,y)))
         == Sum(n_, |x| (|w| g(w, n_ as int))(x) + (|w| Sum(n_, |y| g(w,y)))(x)))
{
}

proof fn L(n: nat, n_: nat, g: spec_fn(int, int) -> int)
    requires(n == n_ + 1)
    ensures(Sum(n, |x| Sum(n, |y| g(x,y)))
         == Sum(n_, |x| Sum(n_, |y| g(x,y))) + Sum(n_, |x| g(x, n_ as int)) + Sum(n_, |y| g(n_ as int,y)) + g(n_ as int, n_ as int))
{
}

proof fn Commute(n: nat, g: spec_fn(int, int) -> int)
    ensures(Sum(n, |x| Sum(n, |y| g(x,y))) == Sum(n, |x| Sum(n, |y| g(y,x))))
{
}

proof fn CommuteSum(n: nat, g: spec_fn(int, int) -> int)
    ensures(Sum(n, |x| Sum(n, |y| g(x,y))) == Sum(n, |y| Sum(n, |x| g(x,y))))
{
}