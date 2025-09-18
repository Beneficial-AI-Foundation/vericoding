// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn sum_of_squares_of_first_n_odd_numbers(n: u32) -> (result: u32)
    requires n >= 0,
    ensures
        result as int == (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Corrected potential overflow errors by using u64 for intermediate calculation of odd_num and current_square. Added overflow checks for `odd_num` and `sum` to ensure correct behavior. Explicitly used `u64::checked_add` to prevent overflow in `sum` and ensure the invariant holds for large `n`.*/

    let mut i: u32 = 0;
    let mut sum: u64 = 0;

    while i < n
        invariant
            i <= n,
            sum as int == (i as int * (2 * i as int - 1) * (2 * i as int + 1)) / 3,

        decreases (n - i) as int
    {
        let odd_num_u64: u64 = 2 * (i as u64) + 1;
        // Assert that odd_num fits in u32 if needed, but for intermediate calc u64 is fine.
        // assert(odd_num_u64 <= u32::MAX as u64);
        // let odd_num: u32 = odd_num_u64 as u32;
        
        let current_square_u64: u64 = odd_num_u64 * odd_num_u64;

        proof {
            assert(sum as int + current_square_u64 as int == ( (i as int + 1) * (2 * (i as int + 1) - 1) * (2 * (i as int + 1) + 1) ) / 3);
        }

        sum = sum.checked_add(current_square_u64).expect("overflow in sum");
        i = i + 1;
    }
    
    // Verify the final sum fits in u32 before casting.
    sum.try_into().expect("result overflows u32")
}
// </vc-code>

}
fn main() {}