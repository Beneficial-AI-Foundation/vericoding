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
exec fn ceil_div_exec(a: i64, b: i64) -> (res: i64)
    requires
        b > 0,
        a >= 0,
    ensures
        res as int == ceil_div(a as int, b as int),
        res >= 0
{
    if a == 0 {
        0
    } else {
        let d = a / b;
        let r = a % b;
        if r == 0 { d } else { d + 1 }
    }
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
    /* code modified by LLM (iteration 5): Use i64 for temporary calculations to avoid overflow */
    let mm: i64 = n as i64;
    let kk: i64 = k as i64;
    let c2: i64 = ceil_div_exec(2 * mm, kk);
    let c5: i64 = ceil_div_exec(5 * mm, kk);
    let c8: i64 = ceil_div_exec(8 * mm, kk);
    let total: i64 = c2 + c5 + c8;
    total as i8
}
// </vc-code>


}

fn main() {}