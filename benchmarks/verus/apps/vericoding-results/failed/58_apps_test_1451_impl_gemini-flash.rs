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

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, numbers: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, k as int, numbers@.map(|i: int, x: i8| x as int))
    ensures 0 <= result as int <= n as int
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type issue by casting k to int before comparison. */
{
    let mut count: i8 = 0;
    let mut i: i8 = 0;

    while i < n
        invariant
            0 <= i as int <= n as int,
            0 <= count as int <= i as int,
            count as int == count_valid_numbers(numbers@.map(|idx, x| x as int), k as int, i as int),

        decreases (n as int) - (i as int)
    {
        let current_num_i8 = numbers[i as usize];
        let ghost current_num_int: int = current_num_i8 as int;
        if count_lucky_digits(current_num_int) <= k as int {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}
// </vc-code>


}

fn main() {}