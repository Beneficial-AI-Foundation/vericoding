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
/* helper modified by LLM (iteration 5): fixed type annotation for literals in proof */
fn exec_count_non_zero_digits(x: i8) -> (count: i8)
    requires
        x >= 0,
    ensures
        count as int == count_non_zero_digits(x as int)
{
    let x0 = x;
    let mut current = x;
    let mut count = 0;
    while current != 0
        invariant
            current >= 0,
            count as int + count_non_zero_digits(current as int) == count_non_zero_digits(x0 as int),
        decreases current
    {
        let digit = current % 10;
        let old_current = current;
        if digit != 0 {
            count += 1;
        }
        current = current / 10;
        proof {
            assert(count_non_zero_digits(old_current as int) == 
                (if digit != 0 { 1int } else { 0int }) + count_non_zero_digits(current as int));
        }
    }
    count
}
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
/* code modified by LLM (iteration 4): fixed overflow by using i16 for loop counter */
{
    let mut count = 0;
    let mut i: i16 = 1;
    while i <= n as i16
        invariant
            1 <= i && i <= (n as i16) + 1,
            count as int == count_range(n as int, k as int, 1, (i - 1) as int),
            count as int >= 0,
            count as int <= (i - 1) as int,
        decreases (n as i16) - i + 1
    {
        if exec_count_non_zero_digits(i as i8) == k {
            count += 1;
        }
        i += 1;
    }
    count
}
// </vc-code>


}

fn main() {}