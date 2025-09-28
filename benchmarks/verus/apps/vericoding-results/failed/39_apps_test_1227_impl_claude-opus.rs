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
/* helper modified by LLM (iteration 5): Fixed digit count bounds */
fn count_non_zero_digits_exec(n: i8) -> (result: i8)
    requires
        n >= 0,
        n <= 127
    ensures
        result >= 0,
        result <= 3,
        result as int == count_non_zero_digits(n as int)
{
    let mut count: i8 = 0;
    let mut num = n;
    
    while num > 0
        invariant
            0 <= num <= n,
            0 <= count,
            count <= 3,
            count as int + count_non_zero_digits(num as int) == count_non_zero_digits(n as int)
        decreases num
    {
        if num % 10 != 0 {
            count = count + 1;
        }
        num = num / 10;
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
/* code modified by LLM (iteration 5): Removed invalid invariant_except_break syntax */
{
    let mut count: i8 = 0;
    let mut i: i8 = 1;
    
    while i <= n
        invariant
            1 <= i <= n + 1,
            0 <= count,
            count <= n,
            count as int == count_range(n as int, k as int, 1, (i - 1) as int)
        decreases n - i + 1
    {
        let non_zero_count = count_non_zero_digits_exec(i);
        if non_zero_count == k {
            count = count + 1;
        }
        i = i + 1;
    }
    
    count
}
// </vc-code>


}

fn main() {}