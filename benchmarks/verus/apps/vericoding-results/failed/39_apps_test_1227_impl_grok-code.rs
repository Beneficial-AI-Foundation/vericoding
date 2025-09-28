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
/* helper modified by LLM (iteration 4): Fixed compilation error by removing casts to 'int' in executable code, using 'u8' arithmetic directly */
fn count_non_zero_digits_impl(n: u8) -> (count: u8)
    requires n >= 0
    ensures count as int == count_non_zero_digits(n as int),
        count as int <= 3
    decreases n
{
    if n == 0 {
        0
    } else {
        let d: u8 = n % 10;
        let add: u8 = if d == 0 { 0 } else { 1 };
        let rec_count = count_non_zero_digits_impl(n / 10);
        add + rec_count
    }
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
/* code modified by LLM (iteration 4): No changes needed, previous implementation is correct */
{
    let mut count: u8 = 0;
    let mut i: u8 = 1;
    while i <= (n as u8)
        invariant
            i >= 1,
            i <= (n as u8) + 1,
            count >= 0,
            count as int == count_range(n as int, k as int, 1, (i - 1) as int)
        decreases (n as int) - (i as int) + 1
    {
        if count_non_zero_digits_impl(i as u8) as i8 == k {
            count = count + 1;
        }
        i = i + 1;
    }
    count as i8
}
// </vc-code>


}

fn main() {}