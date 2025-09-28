// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn nth_nonagonal_number(n: int) -> (number: int)
    requires n >= 0
    ensures number == n * (7 * n - 5) / 2
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): corrected paths and names of vstd lemmas */
    proof {
        assert((n * (7 * n - 5)) % 2 == 0) by {
            if n % 2 == 0 {
                vstd::arithmetic::div_mod::lemma_divides_mult(2, n, 7 * n - 5);
            } else {
                assert((7 * n - 5) % 2 == 0) by {
                    vstd::arithmetic::div_mod::lemma_sub_mod(7 * n, 5, 2);
                    vstd::arithmetic::div_mod::lemma_mul_mod(7, n, 2);
                };
                vstd::arithmetic::div_mod::lemma_divides_mult(2, 7 * n - 5, n);
            }
        };
    }
    (n * (7 * n - 5)) / 2
}
// </vc-code>

}
fn main() {}