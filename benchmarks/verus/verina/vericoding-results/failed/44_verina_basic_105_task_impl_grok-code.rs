// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed indexing syntax to use [] for Seq instead of @[] to resolve compilation error. */
spec fn no_overflow(a: Seq<i32>, b: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < a.len() ==> (((a[i] as int) * (b[i] as int)) <= i32::MAX as int) && (((a[i] as int) * (b[i] as int)) >= i32::MIN as int)
}
// </vc-helpers>

// <vc-spec>
fn array_product(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] * b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Implemented loop to compute element-wise product of two vectors with proper invariants and decreases clause. */
    let len = a.len();
    let mut result = Vec::new();
    let mut i = 0;
    while i < len
        invariant
            0 <= i <= len,
            a@.len() == len as int,
            b@.len() == len as int,
            result@.len() == i as int,
            forall|j: int| #![trigger(result@[j])] 0 <= j < i as int ==> result@[j] as int == (a@[j] as int) * (b@[j] as int)
        decreases len - i
    {
        result.push(a[i] * b[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}