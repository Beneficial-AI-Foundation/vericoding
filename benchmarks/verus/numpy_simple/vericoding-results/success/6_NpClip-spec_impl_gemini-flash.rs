// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn clip(a: Vec<i8>, min: i8, max: i8) -> (result: Vec<i8>)
    requires min < max,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a@.len() ==> {
            if a@[i] < min as int {
                result@[i] == min as int
            } else if a@[i] > max as int {
                result@[i] == max as int
            } else {
                result@[i] == a@[i]
            }
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added a decreases clause in the while loop */
    let mut result_vec: Vec<i8> = Vec::new();
    let mut i = 0;

    while i < a.len()
        invariant
            result_vec.len() == i,
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> {
                if a@[j] < min as int {
                    result_vec@[j] == min as int
                } else if a@[j] > max as int {
                    result_vec@[j] == max as int
                } else {
                    result_vec@[j] == a@[j]
                }
            },
        decreases a.len() - i
    {
        let val = a[i];
        let clipped_val: i8;

        if val < min {
            clipped_val = min;
        } else if val > max {
            clipped_val = max;
        } else {
            clipped_val = val;
        }
        result_vec.push(clipped_val);
        i = i + 1;
    }
    result_vec
}
// </vc-code>


}
fn main() {}