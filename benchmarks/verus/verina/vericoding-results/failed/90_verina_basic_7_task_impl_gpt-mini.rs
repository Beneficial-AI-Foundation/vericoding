// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma for inductive step of sum formula */
proof fn lemma_step(i: u32)
    ensures
        (i as int * (2 * i as int - 1) * (2 * i as int + 1)) / 3 + (2 * i as int + 1) * (2 * i as int + 1)
            == ((i as int + 1) * (2 * (i as int + 1) - 1) * (2 * (i as int + 1) + 1)) / 3
{
    let a = i as int;
    // Multiply both sides by 3 to avoid fractions
    assert(3 * ((a * (2*a - 1) * (2*a + 1)) / 3 + (2*a + 1) * (2*a + 1)) == 3 * (((a + 1) * (2*(a + 1) - 1) * (2*(a + 1) + 1)) / 3));
    // Simplify the multiplication by 3
    assert(a * (2*a - 1) * (2*a + 1) + 3 * (2*a + 1) * (2*a + 1) == (a + 1) * (2*a + 1) * (2*a + 3));
    // Factor (2*a + 1)
    assert((2*a + 1) * (a * (2*a - 1) + 3 * (2*a + 1)) == (2*a + 1) * ((a + 1) * (2*a + 3)));
    // Reduce the inner expressions
    assert(a * (2*a - 1) + 3 * (2*a + 1) == (a + 1) * (2*a + 3));
    // Final arithmetic equality
    assert(2*a*a + 5*a + 3 == 2*a*a + 5*a + 3);
}

// </vc-helpers>

// <vc-spec>
fn sum_of_squares_of_first_n_odd_numbers(n: u32) -> (result: u32)
    requires n >= 0,
    ensures
        result as int == (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): loop to accumulate squares of odd numbers with proper invariants */
{
    let mut i: u32 = 0;
    let mut acc: u32 = 0;
    while i < n
        invariant i <= n;
        invariant acc as int == (i as int * (2 * i as int - 1) * (2 * i as int + 1)) / 3;
        decreases n - i;
    {
        let old = i;
        let old_acc = acc;
        let odd = 2 * old + 1;
        acc = acc + odd * odd;
        i = i + 1;
        proof {
            // Re-establish the loop invariant for the incremented i using the lemma
            assert(old_acc as int == (old as int * (2 * old as int - 1) * (2 * old as int + 1)) / 3);
            lemma_step(old);
            assert(acc as int == (i as int * (2 * i as int - 1) * (2 * i as int + 1)) / 3);
        }
    }
    acc
}

// </vc-code>

}
fn main() {}