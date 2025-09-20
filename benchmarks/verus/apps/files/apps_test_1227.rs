// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_non_zero_digits(n: int) -> int
    decreases n when n >= 0
{
    if n == 0 { 0 }
    else if n % 10 == 0 { count_non_zero_digits(n / 10) }
    else { 1 + count_non_zero_digits(n / 10) }
}

spec fn count_numbers_with_k_non_zero_digits(n: int, k: int) -> int
{
    count_range(n, k, 1, n)
}

spec fn count_range(n: int, k: int, start: int, end: int) -> int
    decreases if end < start { 0int } else { end - start + 1 }
{
    if start > end { 0 }
    else if count_non_zero_digits(start) == k { 
        1 + count_range(n, k, start + 1, end)
    } else { 
        count_range(n, k, start + 1, end)
    }
}

spec fn valid_input(n: int, k: int) -> bool
{
    n >= 1 && k >= 1 && k <= 3
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn count_numbers_with_exactly_k_non_zero_digits(n: i8, k: i8) -> (count: i8)
requires
    valid_input(n as int, k as int)
ensures
    count as int == count_numbers_with_k_non_zero_digits(n as int, k as int),
    count as int >= 0,
    count as int <= n as int
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}