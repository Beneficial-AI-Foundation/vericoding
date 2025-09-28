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
fn gcd_impl(a: i8, b: i8) -> (result: i8)
    requires
        a > 0,
        b >= 0,
    ensures
        result as int == gcd(a as int, b as int),
    decreases b as int
{
    if b == 0 {
        a
    } else {
        gcd_impl(b, (a % b))
    }
}

fn lcm_impl(a: i8, b: i8) -> (result: i8)
    requires
        a > 0,
        b > 0,
        (a as int * b as int) / gcd(a as int, b as int) <= 127,
    ensures
        result as int == lcm(a as int, b as int),
{
    let g = gcd_impl(a, b);
    (a * b) / g
}

/* helper modified by LLM (iteration 5): Added decreases clause to while loop */
fn lcm_seq_impl(nums: &Vec<i8>) -> (result: i8)
    requires
        nums.len() > 0,
        forall|i: int| 0 <= i < nums.len() ==> nums[i] > 0,
        lcm_seq(nums@.map(|i: int, v: i8| v as int)) <= 127,
    ensures
        result as int == lcm_seq(nums@.map(|i: int, v: i8| v as int)),
    decreases nums.len()
{
    if nums.len() == 1 {
        nums[0]
    } else {
        let first = nums[0];
        let mut rest: Vec<i8> = Vec::new();
        let mut i: usize = 1;
        while i < nums.len()
            invariant
                1 <= i <= nums.len(),
                rest.len() == i - 1,
                forall|j: int| 0 <= j < rest.len() ==> rest[j] == nums[j + 1],
                forall|j: int| 0 <= j < rest.len() ==> rest[j] > 0,
            decreases nums.len() - i
        {
            rest.push(nums[i]);
            i = i + 1;
        }
        assert(rest@.map(|i: int, v: i8| v as int) == nums@.map(|i: int, v: i8| v as int).skip(1));
        let rest_lcm = lcm_seq_impl(&rest);
        lcm_impl(first, rest_lcm)
    }
}
// </vc-helpers>

// <vc-spec>
fn find_minimum_time(periods: Vec<i8>) -> (result: i8)
    requires valid_input(periods@.map(|i: int, v: i8| v as int))
    ensures correct_result(periods@.map(|i: int, v: i8| v as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Call helper function directly */
    lcm_seq_impl(&periods)
}
// </vc-code>


}

fn main() {}