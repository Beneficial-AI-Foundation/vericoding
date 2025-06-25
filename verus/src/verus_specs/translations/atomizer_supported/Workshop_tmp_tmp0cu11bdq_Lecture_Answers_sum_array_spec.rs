// ATOM 
spec fn sumTo(a: &[int], n: int) -> int
    requires 0 <= n && n <= a.len()
{
    if n == 0 { 0 } else { sumTo(a, n-1) + a[n-1] }
}

// SPEC 
pub fn sum_array(a: &[int]) -> (sum: int)
    ensures(sum == sumTo(a, a.len()))
{
}