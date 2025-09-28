// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn product_prefix(a: Seq<int>, end: int) -> int
    decreases end
{
    if end <= 0 {
        1
    } else if end == 1 {
        a[0]
    } else {
        product_prefix(a, end - 1) * a[end - 1]
    }
}

fn cumprod(a: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] as int == product_prefix(a@.map(|_index, x: i8| x as int), i + 1),
        forall|i: int, j: int| 0 <= i < a.len() && j == i + 1 && j < a.len() ==> 
            result[j] as int == (result[i] as int) * (a[j] as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed the initial assignment of `current_product` to correct the loop invariant. */
    let mut result: Vec<i8> = Vec::new();
    result.reserve(a.len());
    let mut i = 0;
    let mut current_product_tracked: i8 = 1;
    let mut ghost current_product: int = 1;

    while i < a.len()
        invariant
            result.len() == i,
            result.len() <= a.len(),
            current_product == product_prefix(a@.map(|_index, x: i8| x as int), i),
            forall|j: int| 0 <= j < i ==> result[j] as int == product_prefix(a@.map(|_index, x: i8| x as int), j + 1),
            0 <= i <= a.len(),
            current_product_tracked as int == current_product
    {
        if i == 0 {
            // The current_product starts at 1, but for i=0, the prefix product is a[0].
            // So, for the first element, we directly assign a[0] to current_product.
            // We need to re-establish the invariant current_product_tracked == current_product after this change.
            current_product = a[i] as int;
            current_product_tracked = a[i];
        } else {
            current_product = current_product * (a[i] as int);
            current_product_tracked = current_product_tracked * a[i];
        }
        result.push(current_product_tracked);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}