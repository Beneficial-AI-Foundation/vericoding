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
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
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
        let val = if a[i] < min {
            min
        } else if a[i] > max {
            max
        } else {
            a[i]
        };
        result.push(val);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}