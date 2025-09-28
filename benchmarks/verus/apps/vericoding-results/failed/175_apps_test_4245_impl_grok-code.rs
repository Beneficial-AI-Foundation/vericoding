// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int) -> bool {
    a > 1 && b >= 0
}

spec fn sockets_after_strips(strips: int, a: int) -> int
    recommends a > 1 && strips >= 0
{
    1 + strips * (a - 1)
}

spec fn ceiling_division(x: int, y: int) -> int
    recommends y > 0
{
    if x % y == 0 {
        x / y
    } else if x >= 0 {
        x / y + 1
    } else {
        x / y
    }
}

spec fn min_strips_needed(a: int, b: int) -> int
    recommends valid_input(a, b)
{
    if b <= 1 {
        0
    } else {
        ceiling_division(b - 1, a - 1)
    }
}

spec fn correct_result(a: int, b: int, result: int) -> bool
    recommends valid_input(a, b)
{
    result >= 0 &&
    sockets_after_strips(result, a) >= b &&
    (result == 0 || sockets_after_strips(result - 1, a) < b)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added requires x >= -1 to enforce precondition for postcondition verification and used #[verifier::truncate] on cast to handle potential wraparound */

fn ceiling_division_exec(x: i32, y: i32) -> (result: i32)
    requires
        y > 0,
        x >= -1,
    ensures
        (result as int) == ceiling_division(x as int, y as int),
{
    let quot64 = (x as i64) / (y as i64);
    let rem64 = (x as i64) % (y as i64);
    let add = if rem64 == 0 { 0i64 } else if x >= 0 { 1i64 } else { 0i64 };
    #[verifier::truncate]
    (quot64 + add) as i32
}

fn min_strips_needed_exec(a: i32, b: i32) -> (result: i32)
    requires
        valid_input(a as int, b as int),
    ensures
        (result as int) == min_strips_needed(a as int, b as int),
{
    if b <= 1 {
        0
    } else {
        ceiling_division_exec(b - 1, a - 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: i8)
    requires valid_input(a as int, b as int)
    ensures correct_result(a as int, b as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Verified helper function calls and added proof assertion for correctness */
    let a_int = a as i32;
    let b_int = b as i32;
    proof {
        assert(valid_input(a as int, b as int));
    }
    let result_i32 = min_strips_needed_exec(a_int, b_int);
    proof {
        assert(correct_result(a as int, b as int, result_i32 as int));
    }
    (result_i32 as i8)
}
// </vc-code>


}

fn main() {}