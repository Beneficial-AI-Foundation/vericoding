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

proof fn gcd_lemma(a: int, b: int)
    requires a > 0 && b >= 0
    ensures gcd(a, b) > 0
    decreases b when b >= 0
{
    if b > 0 {
        gcd_lemma(b, a % b);
    }
}

proof fn lcm_lemma(a: int, b: int)
    requires a > 0 && b > 0
    ensures lcm(a, b) > 0 && lcm(a, b) % a == 0 && lcm(a, b) % b == 0
{
    gcd_lemma(a, b);
}

proof fn lcm_seq_lemma(nums: Seq<int>)
    requires nums.len() > 0 && forall|i: int| 0 <= i < nums.len() ==> nums[i] > 0
    ensures lcm_seq(nums) > 0
    decreases nums.len()
{
    if nums.len() > 1 {
        lcm_seq_lemma(nums.skip(1));
        lcm_lemma(nums[0], lcm_seq(nums.skip(1)));
    }
}

fn lcm_u8(a: i8, b: i8) -> (result: i8)
    requires a > 0 && b > 0
    ensures result > 0 && result as int == lcm(a as int, b as int)
{
    let a_val = a as u8;
    let b_val = b as u8;
    let gcd_val = gcd_u8(a_val, b_val);
    let result_val = (a_val as u16 * b_val as u16) / gcd_val as u16;
    assert(result_val <= i8::MAX as u16) by {
        assert(a_val <= i8::MAX as u8);
        assert(b_val <= i8::MAX as u8);
        gcd_lemma(a as int, b as int);
        assert(gcd_val as int == gcd(a as int, b as int));
        assert((a as int * b as int) / gcd(a as int, b as int) <= i8::MAX as int);
    };
    result_val as i8
}

/* helper modified by LLM (iteration 5): added decreases clause */
fn gcd_u8(a: u8, b: u8) -> (gcd_val: u8)
    requires a > 0 && b >= 0
    ensures gcd_val > 0
{
    let mut x = a;
    let mut y = b;
    while y > 0
        invariant
            x > 0,
            y >= 0,
            gcd(x as int, y as int) == gcd(a as int, b as int)
        decreases y
    {
        let temp = y;
        y = x % y;
        x = temp;
    }
    x
}

// </vc-helpers>

// <vc-spec>
fn find_minimum_time(periods: Vec<i8>) -> (result: i8)
    requires valid_input(periods@.map(|i: int, v: i8| v as int))
    ensures correct_result(periods@.map(|i: int, v: i8| v as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed while loop invariant */
    let mut result = periods[0];
    let mut i: usize = 1;
    
    while i < periods.len()
        invariant
            0 <= i <= periods.len(),
            result > 0,
            result as int == lcm_seq(periods@.subrange(0, i as int).map(|k: int, v: i8| v as int))
        decreases periods.len() - i
    {
        proof {
            lcm_seq_lemma(periods@.subrange(0, i as int).map(|k: int, v: i8| v as int));
        }
        result = lcm_u8(result, periods[i]);
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}