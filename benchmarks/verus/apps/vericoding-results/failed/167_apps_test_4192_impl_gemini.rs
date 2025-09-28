// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(d: int, t: int, s: int) -> bool {
    1 <= d <= 10000 && 1 <= t <= 10000 && 1 <= s <= 10000
}

spec fn can_travel(d: int, t: int, s: int) -> bool {
    d <= t * s
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(d: i8, t: i8, s: i8) -> (result: &'static str)
    requires 
        valid_input(d as int, t as int, s as int),
    ensures 
        can_travel(d as int, t as int, s as int) ==> result == "Yes",
        !can_travel(d as int, t as int, s as int) ==> result == "No",
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [Corrected the path to lemma_mul_fits to fix compilation.] */
    proof {
        // The `requires` clause and `i8` types constrain `t` and `s` to the range [1, 127].
        // Their mathematical product `(t as int) * (s as int)` is in [1, 16129], which fits in `i32`.
        // `lemma_mul_fits` proves that the `i32` multiplication does not overflow
        // and matches the result of the mathematical multiplication.
        vstd::arithmetic::mul::lemma_mul_fits::<i32>(t as int, s as int);
    }
    
    if (d as i32) <= (t as i32) * (s as i32) {
        "Yes"
    } else {
        "No"
    }
}

// </vc-code>


}

fn main() {}