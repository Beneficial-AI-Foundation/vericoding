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
/* helper modified by LLM (iteration 5): proof that gcd of positive ints is positive */
fn gcd_pos(a: int, b: int)
    requires a > 0 && b >= 0,
    ensures gcd(a, b) > 0,
    decreases b
{
    proof {
        if b != 0 {
            assert(gcd(a, b) == gcd(b, a % b));
            gcd_pos(b, a % b);
            assert(gcd(b, a % b) > 0);
            assert(gcd(a, b) > 0);
        } else {
            assert(gcd(a, b) == a);
            assert(a > 0);
        }
    }
}

/* helper modified by LLM (iteration 5): proof that lcm of positive ints is positive */
fn lcm_pos(a: int, b: int)
    requires a > 0 && b > 0,
    ensures lcm(a, b) > 0,
{
    proof {
        gcd_pos(a, b);
        assert(gcd(a, b) > 0);
        assert((a * b) / gcd(a, b) > 0);
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
    /* code modified by LLM (iteration 5): compute runtime lcm with tracked invariant linking runtime and spec */
    let len_usize: usize = periods.len();
    if len_usize == 0 {
        1i8
    } else {
        // spec-level sequence of ints for proofs
        let tracked seq: Seq<int> = periods@.map(|i: int, v: i8| v as int);

        // runtime accumulator (primitive) and tracked accumulator (spec)
        let mut res_rt: i128 = periods[0] as i128;
        tracked let mut res_spec: int = seq[0];

        let mut i: usize = 1usize;
        while i < len_usize
            invariant
                1usize <= i && i <= len_usize,
                res_spec == res_rt as int,
            decreases len_usize - i
        {
            let next_rt: i128 = periods[i] as i128;
            tracked let next_spec: int = seq[i as int];

            // compute runtime gcd of res_rt and next_rt
            let mut a: i128 = if res_rt >= 0 { res_rt } else { -res_rt };
            let mut b: i128 = if next_rt >= 0 { next_rt } else { -next_rt };
            while b != 0
                invariant
                    a >= 0,
                    b >= 0,
                decreases b
            {
                let tmp: i128 = a % b;
                a = b;
                b = tmp;
            }
            let gcd_rt: i128 = a;

            // update runtime lcm
            res_rt = (res_rt * next_rt) / gcd_rt;

            // update tracked spec accumulator to reflect runtime value
            tracked res_spec = res_rt as int;

            i = i + 1usize;
        }

        // final runtime result cast to i8 (primitive-to-primitive cast)
        res_rt as i8
    }
}

// </vc-code>


}

fn main() {}