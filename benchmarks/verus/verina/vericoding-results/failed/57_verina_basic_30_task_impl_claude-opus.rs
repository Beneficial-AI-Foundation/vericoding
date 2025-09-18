// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn element_wise_modulo(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires
        a.len() == b.len(),
        a.len() > 0,
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed indexing to use usize instead of int */
    let mut result = Vec::new();
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == a.len(),
            n == b.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == a[j] % b[j],
            forall|j: int| 0 <= j < b.len() ==> b[j] != 0,
        decreases n - i
    {
        assert(0 <= i < b.len());
        assert(b[i as int] != 0);
        let val = a[i] % b[i];
        result.push(val);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}