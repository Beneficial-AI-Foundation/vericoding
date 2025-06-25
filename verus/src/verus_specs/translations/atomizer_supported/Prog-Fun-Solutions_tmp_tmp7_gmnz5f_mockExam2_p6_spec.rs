spec fn f(n: int) -> int {
    if n <= 0 { 1 } else { n + f(n-1)*f(n-2) }
}

spec fn fSum(n: nat) -> int {
    if n <= 0 { 0 } else { f(n-1) + fSum(n-1) }
}

pub fn problem6(n: nat) -> (a: int)
    ensures(a == fSum(n))
{
}