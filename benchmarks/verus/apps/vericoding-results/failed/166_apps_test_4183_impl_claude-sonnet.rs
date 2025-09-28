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
        result as int == gcd(a as int, b as int)
    decreases b
{
    if b == 0 {
        a
    } else {
        gcd_impl(b, a % b)
    }
}

fn lcm_impl(a: i8, b: i8) -> (result: i8)
    requires
        a > 0,
        b > 0,
    ensures
        result as int == lcm(a as int, b as int)
{
    (a * b) / gcd_impl(a, b)
}

lemma lemma_lcm_associative(a: int, b: int, c: int)
    requires
        a > 0,
        b > 0,
        c > 0,
    ensures lcm(a, lcm(b, c)) == lcm(lcm(a, b), c)
{
}

lemma lemma_lcm_seq_fold(nums: Seq<int>)
    requires
        nums.len() > 0,
        forall|i: int| 0 <= i < nums.len() ==> nums[i] > 0,
    ensures
        lcm_seq(nums) > 0
    decreases nums.len()
{
    if nums.len() == 1 {
    } else {
        lemma_lcm_seq_fold(nums.skip(1));
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
    let mut result: i8 = periods[0];
    let mut i: usize = 1;
    
    while i < periods.len()
        invariant
            0 < i,
            i <= periods.len(),
            result > 0,
            result as int == lcm_seq(periods@.subrange(0, i as int).map(|j: int, v: i8| v as int)),
        decreases periods.len() - i
    {
        result = lcm_impl(result, periods[i]);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}