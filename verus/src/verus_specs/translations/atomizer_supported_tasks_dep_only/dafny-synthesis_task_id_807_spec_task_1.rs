// ATOM 
spec fn IsOdd(x: int) -> bool
{
    x % 2 != 0
}

// SPEC 
pub fn FindFirstOdd(a: &[int]) -> (found: bool, index: int)
    requires(true)
    ensures(|result: (bool, int)| {
        let (found, index) = result;
        (!found ==> forall|i: int| 0 <= i < a.len() ==> !IsOdd(a[i as usize])) &&
        (found ==> 0 <= index < a.len() && IsOdd(a[index as usize]) && forall|i: int| 0 <= i < index ==> !IsOdd(a[i as usize]))
    })
{
}