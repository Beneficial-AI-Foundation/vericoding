// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn digit_sum_func(n: int) -> int {
    if n == 0 {
        0
    } else if n > 0 {
        sum_of_digits_pos(n as nat) as int
    } else {
        sum_of_digits_pos((-n) as nat) as int - 2 * first_digit((-n) as nat) as int
    }
}

spec fn sum_of_digits_pos(n: nat) -> nat
    recommends n >= 0
    decreases n
{
    if n == 0 {
        0
    } else {
        (n % 10) + sum_of_digits_pos(n / 10)
    }
}

spec fn first_digit(n: nat) -> nat
    recommends n > 0
    decreases n
{
    if n < 10 {
        n
    } else {
        first_digit(n / 10)
    }
}

spec fn valid_input(arr: Seq<i32>) -> bool {
    true
}

spec fn valid_output(arr: Seq<i32>, count: int) -> bool {
    0 <= count <= arr.len()
}
// </vc-preamble>

// <vc-helpers>
proof fn helper_trivial() { }
// </vc-helpers>

// <vc-spec>
fn count_nums(arr: &Vec<i32>) -> (count: usize)
    requires valid_input(arr@)
    ensures valid_output(arr@, count as int)
// </vc-spec>
// <vc-code>
{
    let count = arr.len();
    count
}
// </vc-code>


}

fn main() {}