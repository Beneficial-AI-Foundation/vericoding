// ATOM 
spec fn sumNegativesTo(a: &[int], n: int) -> int
    requires 0 <= n && n <= a.len()
{
    if n == 0 { 0 } else if a[n-1] < 0 { sumNegativesTo(a, n-1) + a[n-1] } else { sumNegativesTo(a, n-1) }
}

// SPEC
pub fn SumOfNegatives(a: &[int]) -> (result: int)
    ensures(result == sumNegativesTo(a, a.len() as int))
{
}