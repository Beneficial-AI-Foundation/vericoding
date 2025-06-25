// ATOM
spec fn countTo(a: &[bool], n: int) -> int
    recommends 0 <= n <= a.len()
{
    if n == 0 { 0 } else { countTo(a, n-1) + if a[n-1] { 1 } else { 0 } }
}

// SPEC
pub fn CountTrue(a: &[bool]) -> (result: int)
    ensures(result == countTo(a, a.len() as int))
{
}