// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, a: int, b: int, c: int, d: int, e: int) -> bool {
    n >= 1 && a >= 1 && b >= 1 && c >= 1 && d >= 1 && e >= 1
}

spec fn min_capacity(a: int, b: int, c: int, d: int, e: int) -> int
    recommends a >= 1 && b >= 1 && c >= 1 && d >= 1 && e >= 1
{
    let temp1 = if a <= b { a } else { b };
    let temp2 = if temp1 <= c { temp1 } else { c };
    let temp3 = if temp2 <= d { temp2 } else { d };
    if temp3 <= e { temp3 } else { e }
}

spec fn ceil_div(a: int, b: int) -> int
    recommends a >= 0 && b >= 1
{
    (a + b - 1) / b
}

spec fn correct_result(n: int, a: int, b: int, c: int, d: int, e: int, result: int) -> bool
    recommends valid_input(n, a, b, c, d, e)
{
    let min_cap = min_capacity(a, b, c, d, e);
    let groups = ceil_div(n, min_cap);
    result == 4 + groups
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Modified to use i64 for calculations to prevent overflow */
fn min_capacity_exec(a: i8, b: i8, c: i8, d: i8, e: i8) -> i64
{
    let a64 = a as i64;
    let b64 = b as i64;
    let c64 = c as i64;
    let d64 = d as i64;
    let e64 = e as i64;
    let temp1 = if a64 <= b64 { a64 } else { b64 };
    let temp2 = if temp1 <= c64 { temp1 } else { c64 };
    let temp3 = if temp2 <= d64 { temp2 } else { d64 };
    if temp3 <= e64 { temp3 } else { e64 }
}

fn ceil_div_exec(a: i8, b: i64) -> i64
{
    let n64 = a as i64;
    (n64 + b - 1) / b
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8, c: i8, d: i8, e: i8) -> (result: i8)
    requires 
        valid_input(n as int, a as int, b as int, c as int, d as int, e as int)
    ensures 
        correct_result(n as int, a as int, b as int, c as int, d as int, e as int, result as int) &&
        result >= 5
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Implemented main logic using i64 calculations to avoid overflow */
{
    let min_cap = min_capacity_exec(a, b, c, d, e);
    let groups = ceil_div_exec(n, min_cap);
    let result = 4 + groups;
    result as i8
}
// </vc-code>


}

fn main() {}