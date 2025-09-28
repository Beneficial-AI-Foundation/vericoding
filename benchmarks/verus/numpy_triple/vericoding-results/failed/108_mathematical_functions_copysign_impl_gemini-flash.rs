// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [Removed helper functions to simplify the solution.  All logic consolidated within `copysign` function.] */

// </vc-helpers>

// <vc-spec>
fn copysign(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            /* Basic behavior: sign copying with magnitude preservation */
            (x2@[i] >= 0 ==> result@[i] as int == if x1@[i] >= 0 { x1@[i] as int } else { -(x1@[i] as int) }) &&
            (x2@[i] < 0 ==> result@[i] as int == if x1@[i] >= 0 { -(x1@[i] as int) } else { x1@[i] as int }) &&
            /* Magnitude preservation property: |result[i]| = |x1[i]| */
            (if result@[i] >= 0 { result@[i] as int } else { -(result@[i] as int) }) == 
            (if x1@[i] >= 0 { x1@[i] as int } else { -(x1@[i] as int) }) &&
            /* Sign copying property: result has same sign as x2 */
            (x2@[i] >= 0 ==> result@[i] >= 0) &&
            (x2@[i] < 0 ==> result@[i] < 0)
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [Corrected indexing issue: `Vec<i8>` now accessed using `vec.index(i)` for type `i8` values, ensuring proper Rust indexing while preserving `Seq<i8>` behavior in specs.] */
{
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;

    while i < x1.len()
        invariant
            0 <= i as int,
            i as int <= x1.len() as int,
            result.len() == i,
            // All elements processed so far satisfy the conditions
            forall|j: int| 0 <= j < i as int ==> {
                (x2@.index(j) >= 0 ==> result@.index(j) as int == if x1@.index(j) >= 0 { x1@.index(j) as int } else { -(x1@.index(j) as int) }) &&
                (x2@.index(j) < 0 ==> result@.index(j) as int == if x1@.index(j) >= 0 { -(x1@.index(j) as int) } else { x1@.index(j) as int }) &&
                (if result@.index(j) >= 0 { result@.index(j) as int } else { -(result@.index(j) as int) }) == 
                (if x1@.index(j) >= 0 { x1@.index(j) as int } else { -(x1@.index(j) as int) }) &&
                (x2@.index(j) >= 0 ==> result@.index(j) >= 0) &&
                (x2@.index(j) < 0 ==> result@.index(j) < 0)
            }
        decreases x1.len() - i
    {
        // Access Vec elements using .index() method to get the value as i8
        let val_x1 = x1.index(i);
        let val_x2 = x2.index(i);
        
        let mut new_val: i8;

        if val_x2 >= 0 { // Target sign is non-negative
            if val_x1 >= 0 {
                new_val = val_x1;
            } else {
                // val_x1 is negative, make it positive
                new_val = -val_x1;
                proof {
                    assert(new_val as int == -(val_x1 as int));
                    assert(val_x1 < 0 ==> new_val >= 0);
                }
            }
        } else { // Target sign is negative
            if val_x1 < 0 {
                new_val = val_x1;
            } else {
                // val_x1 is non-negative, make it negative
                new_val = -val_x1;
                proof {
                    assert(new_val as int == -(val_x1 as int));
                    assert(val_x1 >= 0 ==> new_val <= 0);
                }
            }
        }

        result.push(new_val);
        i = i + 1;
    }

    result
}
// </vc-code>


}
fn main() {}