// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn repeat<T: Copy>(a: Vec<T>, repeats: usize) -> (result: Vec<T>)
    requires repeats > 0,
    ensures
        result.len() == a.len() * repeats,
        forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> {
            let k = i / (repeats as int);
            0 <= k < a.len() && result[i] == a[k]
        },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added trigger to quantifiers in invariants to allow automatic proof, and made result indexing consistent with @ syntax */
{
    let mut result = Vec::new();
    for i in 0..a.len()
        invariant
            result.len() == i * repeats,
            forall|j: int| #![trigger result@[j]] 0 <= j < result.len() ==> {
                let k = j / (repeats as int);
                result@[j] == a@[k]
            }
    {
        for _ in 0..repeats
            invariant
                result.len() == i * repeats,
                forall|j: int| #![trigger result@[j]] 0 <= j < result.len() ==> {
                    let k = j / (repeats as int);
                    result@[j] == a@[k]
                }
        {
            result.push(a[i]);
        }
    }
    result
}
// </vc-code>

}
fn main() {}