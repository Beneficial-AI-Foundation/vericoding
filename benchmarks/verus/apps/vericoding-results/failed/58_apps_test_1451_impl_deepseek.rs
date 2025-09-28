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
/* helper modified by LLM (iteration 5): Fixed arithmetic overflow and recursive call precondition */
fn count_lucky_digits_recursive(num: i8) -> (result: i8)
    requires num >= 0
    ensures result >= 0 && result <= 10
    decreases num as int
{
    if num == 0 {
        0
    } else {
        let rest = num / 10;
        proof {
            assert(rest >= 0) by {
                assert(num >= 1 ==> rest >= 0);
            };
        }
        let digit_count = if num % 10 == 4 || num % 10 == 7 { 1 } else { 0 };
        let recursive_count = count_lucky_digits_recursive(rest);
        assert(digit_count + recursive_count >= 0 && digit_count + recursive_count <= 10) by {
            assert(recursive_count >= 0 && recursive_count <= 10);
            assert(digit_count >= 0 && digit_count <= 1);
        };
        digit_count + recursive_count
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, numbers: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, k as int, numbers@.map(|i: int, x: i8| x as int))
    ensures 0 <= result as int <= n as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed arithmetic overflow and precondition handling */
    let mut count: i8 = 0;
    let mut i: usize = 0;
    
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            count >= 0 && count <= i as i8,
            count as int == count_valid_numbers(numbers@.map(|i: int, x: i8| x as int), k as int, i as int)
        decreases numbers.len() - i
    {
        let num = numbers[i];
        proof {
            assert(num >= 0) by {
                assert(numbers@[i] > 0);
                assert(num as int == numbers@[i]);
            };
        }
        let lucky_count = count_lucky_digits_recursive(num);
        if lucky_count <= k {
            assert(count + 1 >= 0 && count + 1 <= (i as i8) + 1) by {
                assert(count >= 0 && count <= i as i8);
            };
            count = count + 1;
        }
        i = i + 1;
    }
    
    count
}
// </vc-code>


}

fn main() {}