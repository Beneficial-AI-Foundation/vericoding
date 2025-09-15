// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed FnSpec type conversion for Verus spec functions */
fn vec_map2<T, U, V>(a: &Vec<T>, b: &Vec<U>, f: spec_fn(T, U) -> V) -> (result: Vec<V>)
    requires
        a.len() == b.len()
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == f(#[trigger] a[i], b[i])
{
    let mut result = Vec::new();
    let mut j: usize = 0;
    while j < a.len()
        invariant
            0 <= j <= a.len(),
            result.len() == j,
            forall|i: int| 0 <= i < j ==> result[i] == f(a[i], b[i])
    {
        result.push(f(a[j], b[j]));
        j = j + 1;
    }
    result
}

spec fn multiply(a: int, b: int) -> int {
    a * b
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
/* code modified by LLM (iteration 5): Fixed FnSpec conversion with explicit cast */
{
    vec_map2(a, b, multiply as spec_fn(int, int) -> int)
}
// </vc-code>

}
fn main() {}