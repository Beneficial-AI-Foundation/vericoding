use vstd::prelude::*;

verus! {
    /* code modified by LLM (iteration 4): Fixed proof using proper mathematical reasoning about multiplication monotonicity */
    fn square(n: u32) -> (r: u32)
        requires n <= 46340,
        ensures r == n * n,
    {
        proof {
            assert(n <= 46340);
            assert(46340 * 46340 == 2147395600);
            assert(2147395600 <= 0xFFFFFFFF);  // u32::MAX
            // Use multiplication monotonicity: if 0 <= a <= b, then a * a <= b * b
            assert(n * n <= 46340 * 46340) by {
                // Since n and 46340 are both non-negative u32 values
                // and n <= 46340, multiplication preserves the ordering
                assert(n >= 0 && 46340 >= 0);  // u32 values are non-negative
                // Multiplication monotonicity for non-negative numbers
                assert(n <= 46340 ==> n * n <= n * 46340);
                assert(n * 46340 <= 46340 * 46340);
                // Transitivity: n * n <= n * 46340 <= 46340 * 46340
            };
        }
        n * n
    }
}

#[verifier::external]
fn main() {
    println!("Square function implemented and verified!");
}