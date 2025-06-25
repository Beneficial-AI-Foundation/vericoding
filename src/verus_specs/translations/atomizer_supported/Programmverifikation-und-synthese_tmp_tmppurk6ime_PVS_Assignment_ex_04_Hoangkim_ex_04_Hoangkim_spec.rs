//Problem 01
// SPEC 
//Problem 01
pub fn sumOdds(n: nat) -> (sum: nat)
    requires(n > 0)
    ensures(sum == n * n)
{
}


//problem02
//a)
// SPEC 

//problem02
//a)
pub fn intDiv(n: int, d: int) -> (q: int, r: int)
    requires(n >= d && n >= 0 && d > 0)
    ensures((d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d)
{
}

//b)c)

pub fn intDivImpl(n: int, d: int) -> (q: int, r: int)
    requires(n >= d && n >= 0 && d > 0)
    ensures((d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d)
{
}