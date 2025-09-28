// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed all helpers as they are not needed */
// </vc-helpers>

// <vc-spec>
spec fn vec_product_int(a: Seq<i32>) -> int 
    decreases a.len()
{
    if a.len() == 0 {
        1
    } else {
        (a[0] as int) * vec_product_int(a.skip(1))
    }
}

fn prod(a: Vec<i8>) -> (result: i8)
    ensures 
        result as int == vec_product_int(a@.map(|i, x| x as i32)),
        a.len() == 0 ==> result == 1,
        (exists|i: int| 0 <= i < a.len() && a[i] == 0) ==> result == 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): use i8 arithmetic to avoid ghost code issues */
{
    if a.len() == 0 {
        return 1i8;
    }
    let mut product = 1i8;
    for i in 0..a.len()
        invariant
            0 <= i <= a.len(),
            product as int == vec_product_int(a@.take(i as int).map(|j, x| x as i32)),
    {
        if a[i] == 0 {
            product = 0;
        } else {
            product = product * a[i];
        }
    }
    product
}
// </vc-code>


}
fn main() {}