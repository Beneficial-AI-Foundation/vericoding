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
/* helper modified by LLM (iteration 5): fixed invariant by correctly handling overflow case */
fn count_lucky_digits_impl(num: i8) -> (result: i8)
    requires
        num > 0,
        num <= 127
    ensures
        result as int == count_lucky_digits(num as int),
        result >= 0,
        result <= 3
{
    let mut current = num;
    let mut count = 0i8;
    
    while current > 0
        invariant
            current >= 0,
            count >= 0,
            count <= 3,
            count as int + count_lucky_digits(current as int) == count_lucky_digits(num as int)
        decreases current
    {
        let digit = current % 10;
        if digit == 4 || digit == 7 {
            count = count + 1;
        }
        current = current / 10;
    }
    
    count
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, numbers: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, k as int, numbers@.map(|i: int, x: i8| x as int))
    ensures 0 <= result as int <= n as int
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed invariant by removing overflow guard and using correct bounds */
{
    let mut valid_count = 0i8;
    let mut i = 0i8;
    
    while i < n
        invariant
            0 <= i <= n,
            0 <= valid_count <= i,
            i as int <= n as int,
            valid_count as int == count_valid_numbers(numbers@.map(|i: int, x: i8| x as int), k as int, i as int)
        decreases n - i
    {
        let num_value = numbers[i as usize];
        let lucky_count = count_lucky_digits_impl(num_value);
        if lucky_count <= k {
            valid_count = valid_count + 1;
        }
        i = i + 1;
    }
    
    valid_count
}
// </vc-code>


}

fn main() {}