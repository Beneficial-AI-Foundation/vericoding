// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn product_prefix_lemma(a: Seq<int>, end: int)
    requires
        0 <= end <= a.len(),
    ensures
        product_prefix(a, end) == if end == 0 { 1 } else { product_prefix(a, end - 1) * a[end - 1] },
    decreases end
{
    if end > 0 {
        product_prefix_lemma(a, end - 1);
    }
}

proof fn product_prefix_nonzero(a: Seq<int>, end: int)
    requires
        0 <= end <= a.len(),
        forall|i: int| 0 <= i < end ==> a[i] != 0,
    ensures
        product_prefix(a, end) != 0,
    decreases end
{
    if end > 0 {
        product_prefix_nonzero(a, end - 1);
    }
}
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
    /* code modified by LLM (iteration 5): fix compilation error by avoiding int type in executive code */
    let mut result = Vec::new();
    let mut current_product: i8 = 1;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int == product_prefix(a@.map(|_index, x: i8| x as int), j + 1),
            current_product as int == product_prefix(a@.map(|_index, x: i8| x as int), i),
    {
        current_product = (current_product as i32 * a[i] as i32) as i8;
        result.push(current_product);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}