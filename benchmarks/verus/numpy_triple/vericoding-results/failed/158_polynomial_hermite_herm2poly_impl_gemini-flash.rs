// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The `lemma_herm2poly_rec_step_val` was originally intended to demonstrate the property `(2*i+1) * c_i = (2*i+1) * c_i` which holds automatically. The intent was to show the calculation of values. The lemma's output was fixed by changing `(2 * i + 1) * 1` to `(2 * i + 1) * c_i`. This now correctly reflects multiplication with the `c_i` value.*/
proof fn lemma_herm2poly_rec_step_val(i: int, c_i: int) -> int
    requires i >= 0
    ensures (2 * i + 1) * c_i == (2 * i as int + 1) * c_i
{
    (2 * i + 1) * c_i
}
// </vc-helpers>

// <vc-spec>
fn herm2poly(c: Vec<i8>) -> (result: Vec<i8>)
    requires c.len() > 0,
    ensures
        result.len() == c.len(),
        /* Sanity checks */
        c.len() == 1 ==> result@ == c@,
        c.len() == 2 ==> result[0] == c[0] && result[1] as int == 2 * c[1] as int,
        /* Example from documentation: herm2poly([1, 2.75, 0.5, 0.375]) approximated with integers */
        (c.len() == 4 && c[0] as int == 1 && c[1] as int == 3 && c[2] as int == 1 && c[3] as int == 0) ==>
            (result[0] as int == 0 && result[1] as int == 1 && result[2] as int == 2 && result[3] as int == 3)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The mismatch errors are caused by comparing `result[j as usize]` or `c[j as usize]` (which are `i8`) directly to `int` values without explicit casting. The invariant has been updated to cast `result[j as usize]` and `c[j as usize]` values to `int` before comparison in the `forall` clause. The cast `(2 * c[i] as i8)` in `calculated_val` will not correctly overflow, this expression should be fixed to `(2 * c[i] as i128) as i8` for `i=1` case. Additionally, the `lemma_herm2poly_rec_step_val` call needs to pass `c[i]` value as argument because the `c_i` parameter was added to match the multiplication that happened in the invariant. */
{
    let n = c.len();
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i as int <= n as int,
            result.len() == i,
            // For the elements already processed, result[j] == (2*j+1) * c[j] for j > 1, result[1] == 2*c[1], result[0] == c[0]
            forall|j: int| 0 <= j < i as int ==> (j == 0 && result[j as usize] as int == c[j as usize] as int) || (j == 1 && result[j as usize] as int == 2 * c[j as usize] as int) || (j > 1 && result[j as usize] as int == ((2 * j + 1) * c[j as usize] as int))
        decreases n - i
    {
        let calculated_val: i8;
        if i == 0 {
            calculated_val = c[i];
        } else if i == 1 {
            calculated_val = (2 * c[i] as i128) as i8;
        } else {
            let multiplier: i128 = (2 * i as i128 + 1);
            let val_c_i: i128 = c[i] as i128;
            calculated_val = (multiplier * val_c_i) as i8;
            proof {
                lemma_herm2poly_rec_step_val(i as int, c[i].into());
            }
        }

        result.push(calculated_val);
        i = i + 1;
    }

    result
}
// </vc-code>


}
fn main() {}