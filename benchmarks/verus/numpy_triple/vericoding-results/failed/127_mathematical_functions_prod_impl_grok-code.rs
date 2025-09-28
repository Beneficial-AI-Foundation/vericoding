// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No modifications needed as helpers section is empty */
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
{
    /* code modified by LLM (iteration 5): Changed index variable i to usize for Vec indexing, used int for product calculation to match ensures spec, updated invariant to cast i as int for Seq operations */
    let mut product: int = 1;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i as int <= a.len() as int,
            product == vec_product_int(a@.take(i as int).map(|_, x| x as i32)),
            decreases
                (a.len() as int) - (i as int)
    {
        if a[i] == 0 {
            product = 0;
        } else {
            product = product * (a[i] as int);
        }
        i = i + 1;
    }
    if a.len() == 0 {
        1 as i8
    } else {
        product as i8
    }
}
// </vc-code>


}
fn main() {}