// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): resubmitting helper as it is likely correct */
fn get_correction_update(diff: i8, discont: i8, period: i8) -> (update: i8)
    requires
        discont > 0,
        period > 0,
    ensures
        (diff > discont ==> update == -period),
        (diff < -discont ==> update == period),
        (-discont <= diff <= discont ==> update == 0),
{
    if diff > discont {
        -period
    } else if diff < -discont {
        period
    } else {
        0
    }
}

// </vc-helpers>

// <vc-spec>
fn unwrap(p: Vec<i8>, discont: i8, period: i8) -> (result: Vec<i8>)
    requires 
        discont > 0,
        period > 0,
    ensures
        result.len() == p.len(),
        /* First element is unchanged (if array is non-empty) */
        p.len() > 0 ==> result@[0] == p@[0],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added preconditions to loop invariants to satisfy preconditions of helper function */
    let mut result = Vec::new();
    let len = p.len();

    if len > 0 {
        result.push(p[0]);

        let mut correction: i8 = 0;
        let mut i: usize = 1;

        while i < len
            invariant
                p.len() == len,
                1 <= i <= len,
                result.len() == i,
                len > 0 ==> result@[0] == p@[0],
                discont > 0,
                period > 0,
            decreases len - i
        {
            let diff = p[i].wrapping_sub(p[i - 1]);
            let update = get_correction_update(diff, discont, period);
            correction = correction.wrapping_add(update);
            let new_val = p[i].wrapping_add(correction);
            result.push(new_val);
            i = i + 1;
        }
    }
    
    result
}

// </vc-code>


}
fn main() {}