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
fn count_lucky_digits_exec(mut num: int) -> (res: int)
    requires
        num >= 0,
    ensures
        res == count_lucky_digits(num),
{
    let orig = num;
    let mut count: int = 0;
    while num > 0
        invariant
            count + count_lucky_digits(num) == count_lucky_digits(orig),
        decreases
            num
    {
        let digit = num % 10;
        num = num / 10;
        if digit == 4 || digit == 7 {
            count = count + 1;
        }
    }
    res = count;
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, numbers: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, k as int, numbers@.map(|i: int, x: i8| x as int))
    ensures 0 <= result as int <= n as int
// </vc-spec>
// <vc-code>
{
    let ns = n as int;
    let k_int = k as int;
    let nums_seq = numbers@.map(|i: int, x: i8| x as int);
    let mut i: int = 0;
    let mut cnt: int = 0;
    while i < ns
        invariant
            0 <= i && i <= ns,
            cnt == count_valid_numbers(nums_seq, k_int, i),
        decreases
            ns - i
    {
        let val = numbers[i as usize] as i8;
        let c = count_lucky_digits_exec((val as int));
        if c <= k_int {
            cnt = cnt + 1;
        }
        i = i + 1;
    }
    result = cnt as i8;
}
// </vc-code>


}

fn main() {}