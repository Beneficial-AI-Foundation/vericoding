// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): unused helper, refactored to use Seq */
spec fn array_product_ensures(a: Seq<i32>, b: Seq<i32>, result: Seq<i32>) -> bool {
    result.len() == a.len() &&
    forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] * b[i]
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
    /* code modified by LLM (iteration 5): fixed compilation error and removed flawed 'choose' logic */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == b.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result.view()[j] == a.view()[j] * b.view()[j],
        decreases a.len() - i
    {
        proof {
            let idx = i as int;
            assert(exists|p: i32| p == a.view()[idx] * b.view()[idx]);
        }

        let product = a[i] * b[i];
        result.push(product);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}