use vstd::prelude::*;

spec fn has_count(v: int, a: &[int], n: int) -> int
    decreases n
{
    if n == 0 { 0 } else {
        if a[(n-1) as usize] == v { has_count(v, a, n-1) + 1 } else { has_count(v, a, n-1) }
    }
}

pub fn count(v: int, a: &[int], n: int) -> (r: int)
    requires(n >= 0 && n <= a.len())
    ensures(has_count(v, a, n) == r)
{
}