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
/* helper modified by LLM (iteration 5): changed count type to i8 to avoid overflow and removed final cast */
fn exec_count_lucky_digits(num: i8) -> (count: i8)
    requires num >= 0
    ensures count as int == count_lucky_digits(num as int)
{
    let mut n: i32 = num as i32;
    let mut count: i8 = 0;
    while n > 0
        invariant
            0 <= n,
            count as int + count_lucky_digits(n as int) == count_lucky_digits(num as int),
        decreases n
    {
        let digit = n % 10;
        n = n / 10;
        if digit == 4 || digit == 7 {
            count += 1;
        }
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
/* code modified by LLM (iteration 5): added assertion for num>=0 and kept count as i32 */
{
    let mut i: usize = 0;
    let mut count: i32 = 0;
    while i < numbers.len()
        invariant
            0 <= i as int <= numbers.len() as int,
            count as int == count_valid_numbers(numbers@.map(|i: int, x: i8| x as int), k as int, i as int),
        decreases numbers.len() - i
    {
        let num = numbers[i];
        assert(num >= 0);
        let lucky_count = exec_count_lucky_digits(num);
        if lucky_count <= k {
            count += 1;
        }
        i += 1;
    }
    assert(0 <= count && count <= n as int);
    count as i8
}
// </vc-code>


}

fn main() {}