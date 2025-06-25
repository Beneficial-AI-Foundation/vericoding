// ATOM
spec fn IsOdd(x: int) -> bool
{
    x % 2 != 0
}

// SPEC
pub fn FindFirstOdd(a: &[int]) -> (found: bool, index: int)
    requires(a.len() >= 0)
    ensures(|result: (bool, int)| !result.0 ==> forall|i: int| 0 <= i < a.len() ==> !IsOdd(a[i as usize]))
    ensures(|result: (bool, int)| result.0 ==> 0 <= result.1 < a.len() && IsOdd(a[result.1 as usize]) && forall|i: int| 0 <= i < result.1 ==> !IsOdd(a[i as usize]))
{
}