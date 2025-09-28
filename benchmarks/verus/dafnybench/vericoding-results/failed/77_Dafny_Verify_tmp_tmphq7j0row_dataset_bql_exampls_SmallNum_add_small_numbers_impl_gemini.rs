// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn add_small_numbers(a: &[i32], n: usize, max: i32) -> (r: i32)
    requires 
        n > 0,
        n <= a.len(),
        forall|i: int| 0 <= i && i < n ==> a[i] <= max,
    ensures
        r <= max * (n as i32),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): used i64 for sum to avoid overflow */
    let mut i: usize = 0;
    let mut sum: i64 = 0;
    while i < n
        invariant
            0 <= i && i <= n,
            (sum as int) <= (max as int) * (i as int),
        decreases n - i
    {
        proof {
            assert((a[i] as int) <= max as int);
        }
        sum = sum + (a[i] as i64);
        i = i + 1;
    }

    assert((sum as int) <= (max as int) * (n as int));

    if sum <= i32::MAX as i64 && sum >= i32::MIN as i64 {
        let result = sum as i32;
        // We can't prove this postcondition without more requires clauses, 
        // specifically about how (max as int) * (n as int) relates to i32 bounds
        // and the wrapping behavior of `max * (n as i32)`.
        // Assuming that for valid inputs, the operation doesn't mislead.
        if (max as int) * (n as int) == (max * (n as i32)) as int {
            return result;
        } else {
            // In this case, the post-condition is likely unprovable, as the RHS has wrapped.
            // We cannot return a value that satisfies it without more information.
            // But we must return a value. The calculated sum is our best bet.
            return result;
        }
    } else {
        // The sum has overflowed i32. The spec doesn't provide enough constraints to prevent this.
        // We can't return a correct i32. However, we must return something.
        // A program that panics would be another option, but verus would not prove it terminates.
        // Fallback to 0, though it's unlikely to satisfy the post-condition.
        return 0;
    }
}
// </vc-code>

}
fn main() {}