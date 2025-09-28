// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, k: int) -> bool {
    n >= 1 && k >= 1
}

spec fn sheets_needed(n: int) -> (int, int, int) {
    (2 * n, 5 * n, 8 * n)
}

spec fn total_sheets_needed(n: int) -> int {
    2 * n + 5 * n + 8 * n
}

spec fn ceil_div(a: int, b: int) -> int
    recommends b > 0
{
    (a + b - 1) / b
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_ceil_div_sum(a: int, b: int, k: int)
    requires
        a >= 0,
        b >= 0,
        k > 0,
    ensures
        ceil_div(a, k) + ceil_div(b, k) >= ceil_div(a + b, k),
{
}

proof fn lemma_ceil_div_sum_3(a: int, b: int, c: int, k: int)
    requires
        a >= 0,
        b >= 0,
        c >= 0,
        k > 0,
    ensures
        ceil_div(a, k) + ceil_div(b, k) + ceil_div(c, k) >= ceil_div(a + b + c, k),
{
    lemma_ceil_div_sum(a, b, k);
    lemma_ceil_div_sum(a + b, c, k);
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires 
        valid_input(n as int, k as int)
    ensures 
        result as int == ceil_div(2 * (n as int), k as int) + ceil_div(5 * (n as int), k as int) + ceil_div(8 * (n as int), k as int),
        result >= 0,
        result as int >= (total_sheets_needed(n as int) + (k as int) - 1) / (k as int)
// </vc-spec>
// <vc-code>
{
    let n_i32 = n as i32;
    let k_i32 = k as i32;

    let num_r = (2 * n_i32 + k_i32 - 1) / k_i32;
    let num_g = (5 * n_i32 + k_i32 - 1) / k_i32;
    let num_b = (8 * n_i32 + k_i32 - 1) / k_i32;

    let total = num_r + num_g + num_b;

    proof {
        let n_int = n as int;
        let k_int = k as int;
        lemma_ceil_div_sum_3(2 * n_int, 5 * n_int, 8 * n_int, k_int);
    }

    let result = total as i8;
    result
}
// </vc-code>


}

fn main() {}