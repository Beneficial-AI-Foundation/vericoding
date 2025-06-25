// ATOM 
pub open spec fn IsOdd(n: int) -> bool
{
    n % 2 == 1
}

// SPEC 

pub fn IsOddAtIndexOdd(a: &[int]) -> (result: bool)
    ensures(result <==> forall|i: int| 0 <= i < a.len() ==> (IsOdd(i) ==> IsOdd(a[i as usize])))
{
}