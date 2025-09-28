// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int, numbers: Seq<int>) -> bool {
    n >= 1 && k >= 0 && numbers.len() == n && forall|i: int| 0 <= i < numbers.len() ==> numbers[i] > 0
}

spec fn count_lucky_digits(num: int) -> int
    decreases num when num >= 0
{
    if num <= 0 { 0 }
    else {
        let digit = num % 10;
        let rest = num / 10;
        let digit_count: int = if digit == 4 || digit == 7 { 1 } else { 0 };
        digit_count + count_lucky_digits(rest)
    }
}

spec fn count_valid_numbers(numbers: Seq<int>, k: int, up_to: int) -> int
    decreases up_to when up_to >= 0
{
    if up_to <= 0 { 0 }
    else {
        let prev_count = count_valid_numbers(numbers, k, up_to - 1);
        if count_lucky_digits(numbers[up_to - 1]) <= k { prev_count + 1 } else { prev_count }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed syntax error in decreases clause by removing extra quote */
exec fn count_lucky_digits_exec(num: u32) -> (result: u32)
    requires
        num >= 0,
    ensures
        result as int == count_lucky_digits(num as int),
{
    let mut result = 0u32;
    let mut remaining = num;
    while remaining > 0
        invariant
            result as int == count_lucky_digits(num as int) - count_lucky_digits(remaining as int),
        decreases remaining
    {
        if remaining % 10 == 4 || remaining % 10 == 7 {
            result += 1;
        }
        remaining /= 10;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, numbers: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, k as int, numbers@.map(|i: int, x: i8| x as int))
    ensures 0 <= result as int <= n as int
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): kept implementation unchanged as compilation error was in helpers */
{
    let mut count: i16 = 0;
    let mut i: usize = 0;
    while i < n as usize
        invariant
            0 <= i <= n as usize,
            count as int == count_valid_numbers(numbers@.map(|ii: int, x: i8| x as int), k as int, i as int),
        decreases (n as usize - i)
    {
        let num_u32 = numbers[i] as u32;
        let lucky = count_lucky_digits_exec(num_u32);
        if lucky as i16 <= k as i16 {
            count += 1;
        }
        proof {
            assert(count as int == count_valid_numbers(numbers@.map(|ii: int, x: i8| x as int), k as int, i as int + 1));
        }
        i += 1;
    }
    count as i8
}
// </vc-code>


}

fn main() {}