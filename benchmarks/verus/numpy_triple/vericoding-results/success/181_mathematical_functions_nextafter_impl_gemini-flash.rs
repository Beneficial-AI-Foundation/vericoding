// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Replaced `overflowing_add` and `overflowing_sub` with direct arithmetic operations for `i8` type, as Verus does not support `overflowing_add`. Added asserts for clarity and to guide Verus. */
fn find_next_i8(a: i8, b: i8) -> (result: i8)
    ensures
        (a == b ==> result == a),
        (a < b ==> (a < result && result <= b)),
        (a > b ==> (a > result && result >= b)),
{
    if a == b {
        a
    } else if a < b {
        // If a is `i8::MAX`, then a + 1 would wrap around.
        // If a + 1 is greater than b, it would mean that b is closer, or the target value has exceeded b.
        let potential_next = a + 1;
        if potential_next == b {
            assert(a < potential_next && potential_next <= b);
            b
        } else if potential_next > b {
            assert(a < b); // Sanity check based on the 'a < b' branch
            // This case implies that `b` is 'between' `a` and `a+1` (but it's integer arithmetic).
            // Or that `a+1` has already surpassed `b`. The closest to `a` but towards `b` is `b` itself if `a+1 > b`.
            b
        } else {
            // a < potential_next <= b 
            assert(a < potential_next);
            assert(potential_next <= b);
            potential_next
        }
    } else { // a > b
        let potential_prev = a - 1;
        if potential_prev == b {
            assert(a > potential_prev && potential_prev >= b);
            b
        } else if potential_prev < b {
            assert(a > b); // Sanity check based on the 'a > b' branch
            // Similar logic to the a < b case, if a-1 is less than b, then b is the 'closest' towards b.
            b
        } else {
            // a > potential_prev >= b
            assert(a > potential_prev);
            assert(potential_prev >= b);
            potential_prev
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn nextafter(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            /* Identity case: when x1 equals x2, result equals x1 */
            (x1[i] == x2[i] ==> result[i] == x1[i]) &&
            /* Direction consistency: result moves towards x2 */
            ((x1[i] < x2[i] ==> x1[i] < result[i] && result[i] <= x2[i]) &&
             (x1[i] > x2[i] ==> x1[i] > result[i] && result[i] >= x2[i])) &&
            /* Finiteness preservation: if both inputs are finite and different, result is defined */
            (x1[i] != x2[i] ==> true)
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Adjusted invariant for the `forall` clause by removing redundant `|| (x1[j] > x2[j] ==> x1[j] > result[j] && result[j] >= x2[j])`, as the `nextafter` function already ensures direction consistency. */
{
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant 
            0 <= i as int <= x1.len() as int,
            result.len() == i,
            x1.len() == x2.len(),
            forall|j: int| 0 <= j < i as int ==> {
                (x1[j] == x2[j] ==> result[j] == x1[j]) &&
                ((x1[j] < x2[j] ==> x1[j] < result[j] && result[j] <= x2[j]) &&
                 (x1[j] > x2[j] ==> x1[j] > result[j] && result[j] >= x2[j]))
            },
        decreases x1.len() - i
    {
        let next_val = find_next_i8(x1[i], x2[i]);
        result.push(next_val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}