// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_index(i: int, len: int) -> bool { 0 <= i < len }

/* helper modified by LLM (iteration 5): removed unused addition_properties function */
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
    /* code modified by LLM (iteration 5): fixed bounds checking by ensuring b has sufficient length in invariant */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == b.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j as int] == a[j] + b[j],
        decreases a.len() - i
    {
        let sum = a[i] + b[i];
        result.push(sum);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}