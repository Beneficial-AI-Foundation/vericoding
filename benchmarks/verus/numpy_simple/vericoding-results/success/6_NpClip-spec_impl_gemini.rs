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
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            min < max,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                if a@[j] < min as int {
                    result@[j] == min as int
                } else if a@[j] > max as int {
                    result@[j] == max as int
                } else {
                    result@[j] == a@[j]
                }
            },
        decreases a.len() - i
    {
        let val = a[i];
        let clipped_val;
        if val < min {
            clipped_val = min;
        } else if val > max {
            clipped_val = max;
        } else {
            clipped_val = val;
        }
        result.push(clipped_val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}