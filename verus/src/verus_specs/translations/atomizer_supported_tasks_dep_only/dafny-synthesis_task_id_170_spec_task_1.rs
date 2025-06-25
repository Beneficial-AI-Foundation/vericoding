// ATOM 
spec fn sumTo(a: &[int], start: int, end: int) -> int
    recommends(
        0 <= start && start <= end && end <= a.len()
    )
{
    if start == end { 0 } else { sumTo(a, start, (end-1) as int) + a[(end-1) as int] }
}

// SPEC
pub fn SumInRange(a: &[int], start: int, end: int) -> (sum: int)
    requires(
        0 <= start && start <= end && end <= a.len()
    )
    ensures(|sum: int| 
        sum == sumTo(a, start, end)
    )
{
}