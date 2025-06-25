// ATOM
spec fn sumTo(a: &[int], start: int, end: int) -> int
    requires 0 <= start && start <= end && end <= a.len()
    decreases end - start
{
    if start == end { 0 } else { sumTo(a, start, (end-1) as int) + a[(end-1) as int] }
}

// SPEC
pub fn SumInRange(a: &[int], start: int, end: int) -> (sum: int)
    requires(0 <= start && start <= end && end <= a.len())
    ensures(sum == sumTo(a, start, end))
{
}