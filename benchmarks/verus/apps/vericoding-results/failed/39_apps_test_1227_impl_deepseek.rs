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
proof fn lemma_count_non_zero_digits_recursive(n: int)
    requires
        n >= 0,
    ensures
        count_non_zero_digits(n) == if n == 0 { 0 } else if n % 10 == 0 { count_non_zero_digits(n / 10) } else { 1 + count_non_zero_digits(n / 10) },
    decreases n
{
    if n == 0 {
    } else {
        lemma_count_non_zero_digits_recursive(n / 10);
    }
}

proof fn lemma_count_range_base_case(start: int, end: int, n: int, k: int)
    ensures
        start > end ==> count_range(n, k, start, end) == 0
{
}

proof fn lemma_count_range_step(n: int, k: int, start: int, end: int)
    requires
        start <= end,
    ensures
        count_range(n, k, start, end) == if count_non_zero_digits(start) == k {
            1 + count_range(n, k, start + 1, end)
        } else {
            count_range(n, k, start + 1, end)
        },
    decreases if end < start { 0int } else { end - start + 1 }
{
    lemma_count_non_zero_digits_recursive(start);
    if start <= end {
        lemma_count_range_step(n, k, start + 1, end);
    }
}

/* helper modified by LLM (iteration 5): Removed decreases_when clause and fixed decreases clause */
proof fn lemma_count_non_zero_digits_unsigned(n: u32) -> (ret: int)
    ensures ret == count_non_zero_digits(n as int)
    decreases n
{
    if n == 0 { 
        0 
    } else { 
        let sub = lemma_count_non_zero_digits_unsigned(n / 10);
        if n % 10 == 0 { 
            sub 
        } else { 
            1 + sub 
        }
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
{
    /* code modified by LLM (iteration 5): Fixed verification errors and properly implemented counting logic */
    let mut count_out: i8 = 0;
    let mut current: u32 = 1;
    let n_u32 = n as u32;
    let k_u32 = k as u32;
    
    while current <= n_u32
        invariant
            current >= 1,
            current <= n_u32 + 1,
            count_out as int == count_range(n as int, k as int, 1, current as int - 1),
            count_out >= 0,
            count_out <= n
        decreases n_u32 - current
    {
        let mut num = current;
        let mut digit_count: u32 = 0;
        let mut temp = num;
        
        while temp > 0
            invariant
                digit_count as int == count_non_zero_digits(current as int) - count_non_zero_digits(temp as int),
                temp <= current,
                digit_count >= 0,
                digit_count as int <= count_non_zero_digits(current as int)
            decreases temp
        {
            if temp % 10 != 0 {
                digit_count += 1;
            }
            temp /= 10;
        }
        
        proof {
            lemma_count_non_zero_digits_unsigned(current);
        }
        
        if digit_count == k_u32 {
            count_out += 1;
        }
        
        current += 1;
    }
    
    count_out
}
// </vc-code>


}

fn main() {}