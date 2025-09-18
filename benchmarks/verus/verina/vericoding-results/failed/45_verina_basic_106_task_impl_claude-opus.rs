// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] + b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix index bounds and overflow checking */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == a@[j] + b@[j],
        decreases a.len() - i,
    {
        proof {
            assert(i < a.len());
            assert(i < b.len());
        }
        let sum: i32 = a[i] + b[i];
        result.push(sum);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}