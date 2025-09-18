// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed variable name `out` within ensures clause to `result` */
spec fn single_divmod_spec(x1_val: int, x2_val: int) -> (result: (int, int))
    requires
        x2_val != 0,
    ensures
        ({ let (quotient, remainder) = result; x1_val == x2_val * quotient + remainder &&
        (x2_val > 0 ==> 0 <= remainder && remainder < x2_val) &&
        (x2_val < 0 ==> x2_val < remainder && remainder <= 0)}) 
{
    let quotient_val = x1_val / x2_val;
    let remainder_val = x1_val % x2_val;
    if x2_val > 0 && remainder_val < 0 {
        (quotient_val - 1, remainder_val + x2_val)
    } else if x2_val < 0 && remainder_val > 0 {
        (quotient_val + 1, remainder_val + x2_val)
    } else {
        (quotient_val, remainder_val)
    }
}
// </vc-helpers>

// <vc-spec>
fn divmod(x1: Vec<i32>, x2: Vec<i32>) -> (result: (Vec<i32>, Vec<i32>))
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] != 0,
    ensures ({
        let (quotient, remainder) = result;
        quotient.len() == x1.len() &&
        remainder.len() == x1.len() &&
        forall|i: int| 0 <= i < x1.len() ==> {
            x1[i] == x2[i] * quotient[i] + remainder[i] &&
            (x2[i] > 0 ==> 0 <= remainder[i] && remainder[i] < x2[i]) &&
            (x2[i] < 0 ==> x2[i] < remainder[i] && remainder[i] <= 0)
        }
    })
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type casting errors by removing `as int` and `as i32` for `x1_val` and `x2_val` for ghost variables. */
{
    let mut quotient_vec: Vec<i32> = Vec::new();
    let mut remainder_vec: Vec<i32> = Vec::new();

    quotient_vec.fill_with(|_| 0, x1.len());
    remainder_vec.fill_with(|_| 0, x1.len());

    let ghost mut i: int = 0;
    while (i as usize) < x1.len()
        invariant
            0 <= i && (i as usize) <= x1.len(),
            quotient_vec.len() == x1.len(),
            remainder_vec.len() == x1.len(),
            forall|j: int| 0 <= j && j < i ==> {
                let ghost x1_val_ghost = x1[j as usize] as int;
                let ghost x2_val_ghost = x2[j as usize] as int;
                let (q, r) = single_divmod_spec(x1_val_ghost, x2_val_ghost);
                quotient_vec[j as usize] == q as i32 && remainder_vec[j as usize] == r as i32
            }
    {
        let ghost x1_val_ghost = x1[i as usize] as int;
        let ghost x2_val_ghost = x2[i as usize] as int;

        let (q_spec, r_spec) = single_divmod_spec(x1_val_ghost, x2_val_ghost);

        quotient_vec.set(i as usize, q_spec as i32);
        remainder_vec.set(i as usize, r_spec as i32);
        i = i + 1;
    }
    (quotient_vec, remainder_vec)
}
// </vc-code>

}
fn main() {}