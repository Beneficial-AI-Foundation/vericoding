// ATOM 
spec fn sumTo(a: &[int], n: int) -> int
    recommends
        0 <= n && n <= a.len()
{
    if n == 0 { 0 } else { sumTo(a, n-1) + a[n-1] }
}

// SPEC 
pub fn ArraySum(a: &[int]) -> (result: int)
    ensures(result == sumTo(a, a.len() as int))
{
}