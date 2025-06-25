// ATOM 
spec fn sumInts(n: int) -> int
    recommends n >= 0
{
    if n == 0 {
        0
    } else {
        sumInts(n-1)+n
    }
}

// SPEC 

pub fn SumIntsLoop(n: int) -> (s: int)
    requires(n >= 0)
    ensures(s == sumInts(n))
    ensures(s == n*(n+1)/2)
{
}