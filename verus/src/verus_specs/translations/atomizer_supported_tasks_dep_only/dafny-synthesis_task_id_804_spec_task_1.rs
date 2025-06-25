// ATOM 
pub open spec fn IsEven(n: int) -> bool
{
    n % 2 == 0
}

// SPEC 
pub fn IsProductEven(a: &[int]) -> (result: bool)
    ensures(result <==> exists|i: int| 0 <= i < a.len() && IsEven(a[i as usize]))
{
}