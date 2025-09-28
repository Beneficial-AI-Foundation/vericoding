// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn gcd(a: int, b: int) -> int
    decreases b when b >= 0
{
    if a > 0 && b >= 0 {
        if b == 0 { a } else { gcd(b, a % b) }
    } else {
        1  /* default for invalid input */
    }
}

spec fn lcm(a: int, b: int) -> int {
    if a > 0 && b > 0 {
        (a * b) / gcd(a, b)
    } else {
        1  /* default for invalid input */
    }
}

spec fn lcm_seq(nums: Seq<int>) -> int
    decreases nums.len()
{
    if nums.len() > 0 {
        if nums.len() == 1 { 
            nums[0] 
        } else { 
            lcm(nums[0], lcm_seq(nums.skip(1)))
        }
    } else {
        1  /* default for empty sequence */
    }
}

spec fn valid_input(periods: Seq<int>) -> bool {
    periods.len() > 0 && periods.len() <= 100 &&
    forall|i: int| 0 <= i < periods.len() ==> periods[i] > 0
}

spec fn correct_result(periods: Seq<int>, result: int) -> bool {
    valid_input(periods) ==> result == lcm_seq(periods)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Changed to use i64 to prevent overflow in multiplication and division for lcm computation */
fn exec_gcd(a: i64, b: i64) -> (r: i64)
    requires
        a > 0,
        b >= 0,
    ensures
        r as int == gcd(a as int, b as int)
{
    if b == 0 {
        a
    } else {
        exec_gcd(b, a % b)
    }
}

/* helper modified by LLM (iteration 5): Changed to use i64 to prevent overflow in multiplication and division for lcm computation */
fn exec_lcm(a: i64, b: i64) -> (r: i64)
    requires
        a > 0,
        b > 0,
    ensures
        r as int == lcm(a as int, b as int)
{
    let g = exec_gcd(a, b);
    (a * b) / g
}
// </vc-helpers>

// <vc-spec>
fn find_minimum_time(periods: Vec<i8>) -> (result: i8)
    requires valid_input(periods@.map(|i: int, v: i8| v as int))
    ensures correct_result(periods@.map(|i: int, v: i8| v as int), result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Switched computation to i64 to avoid overflow issues, added targeted assertions based on spec predicates to establish preconditions */
{
    let mut result: i64 = 1;
    let mut i: usize = 0;
    while i < periods.len()
        invariant
            0 <= i <= periods.len(),
            result as int == lcm_seq(periods@.take(i as int).map(|j: int, v: i8| v as int)),
        decreases periods.len() - i
    {
        let p = periods[i] as i64;
        assert(p == periods@[i as int] as i64);
        assert(p > 0);
        assert(result > 0);
        result = exec_lcm(result, p as i64);
        i = i + 1;
        assert(result as int == lcm_seq(periods@.take(i as int).map(|j: int, v: i8| v as int))) by {
            if i == 1 {
                assert(lcm_seq(periods@.take(1).map(|j: int, v: i8| v as int)) == periods@[0] as int);
            } else {
                let prev_lcm = lcm_seq(periods@.take((i-1) as int).map(|j: int, v: i8| v as int));
                let last = periods@[(i-1) as int] as int;
                assert(result as int == lcm(prev_lcm, last));
                assert(lcm_seq(periods@.take(i as int).map(|j: int, v: i8| v as int)) == lcm(prev_lcm, last));
            }
        }
    }
    return result as i8;
}
// </vc-code>


}

fn main() {}