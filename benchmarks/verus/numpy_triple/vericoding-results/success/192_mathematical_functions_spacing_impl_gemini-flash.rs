// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Removed helper. */
// </vc-helpers>

// <vc-spec>
fn spacing(x: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < x@.len() ==> #[trigger] result@[i] as int > 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed invariant not satisfied at end of loop body, and underflow/overflow. */
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            result@.len() == i,
            i <= x.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] as int > 0,
        decreases x.len() - i
    {
        let val = x[i];
        if val == 0 {
            result.push(1);
        } else {
            // For i8, -val can still be within i8 range if val is not i8::MIN
            // If val is i8::MIN (-128), -val would be 128, which is outside i8 range but within u8 range.
            // However, the problem specifies the result must be i8.
            // Since we ensured result value must be > 0, we can use `result.push(val.abs() as i8);`.
            // If val is i8::MIN (-128), val.abs() is 128, which is the problem.
            // The problem statement implies we should return absolute value, and it must be > 0.
            // The problem is about numpy, so it's likely expecting us to treat the absolute value as positive
            // and within the i8 range if possible. Given the constraint that result@[i] as int > 0,
            // we are expected to handle this.

            // If `val` is -128, then `-val` overflows i8. `128` cannot be represented as i8.
            // The prompt states the `spacing` function in numpy for integers returns the absolute value.
            // Since the `ensures` clause mandates `result@[i] as int > 0`, we must return a positive value.
            // For `i8::MIN (-128)`, the absolute value is `128` which is outside the `i8` range.
            // In this specific case, we'll return 127 if the value is -128, to stay within i8 and satisfy `>0`.
            // This isn't strictly how numpy handles it (it would cast to a wider type), but it satisfies the Verus constraints.
            let abs_val_i = if val < 0 {
                if val == i8::MIN { i8::MAX } else { -val }
            } else { val };
            result.push(abs_val_i);
        }
        i = i + 1;
        proof {
             // This ensures the loop invariant for result@.len() == i holds after push and increment.
        }
    }
    result
}
// </vc-code>


}
fn main() {}