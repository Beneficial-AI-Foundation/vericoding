// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed unnecessary helper function to avoid compilation errors and simplify the code. */

// </vc-helpers>

// <vc-spec>
fn mgrid(start: i8, stop: i8, step: i8, n: usize) -> (result: Vec<i8>)
    requires
        step > 0,
        start < stop,
        n == ((stop as int - start as int) / step as int) as usize,
    ensures
        result@.len() == n,
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i] == start as int + i * step as int,
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i] < stop as int,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation errors related to `int` and `nat` types by ensuring all calculations operate within the native `i8` type and use `as` conversions when interacting with properties that expect `usize`. */
{
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            result@.len() == i,
            i <= n,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == start as int + j * step as int,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] < stop as int,

            // For the next iteration, ensure `start + (i * step)` fits in i8
            i < n ==> (start as int + i as int * step as int) <= i8::MAX as int,
            i < n ==> (start as int + i as int * step as int) >= i8::MIN as int,

            // Ensure the term `i * step` fits in i8 before adding to `start`
            i < n ==> (i as int * step as int) <= i8::MAX as int,
            i < n ==> (i as int * step as int) >= i8::MIN as int,

        decreases (n - i) 
    {
        // Perform calculations in i8 type to avoid Verus type system issues with `int` in `exec` code.
        let term_i_step: i8 = (i as i8).checked_mul(step).expect("overflow in i * step");
        let val: i8 = start.checked_add(term_i_step).expect("overflow in start + (i * step)");
        
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}