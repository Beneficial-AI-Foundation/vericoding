// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added lemma to prove product_prefix properties for cumulative products */
proof fn product_prefix_lemma(a: Seq<int>, end: int)
    requires
        0 <= end <= a.len(),
    ensures
        end > 1 ==> product_prefix(a, end) == product_prefix(a, end - 1) * a[end - 1],
    decreases end
{
    if end <= 0 {
    } else if end == 1 {
    } else {
        product_prefix_lemma(a, end - 1);
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
    /* code modified by LLM (iteration 5): Fixed overflow handling by computing product as int and properly handling i8 conversion */
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as int == product_prefix(a@.map(|_index, x: i8| x as int), j + 1),
            forall|j: int, k: int| 0 <= j < i && k == j + 1 && k < i ==> 
                result@[k] as int == (result@[j] as int) * (a@[k] as int),
        decreases a.len() - i
    {
        if i == 0 {
            result.push(a[i]);
            assert(result@[0] as int == a@[0] as int);
            assert(product_prefix(a@.map(|_index, x: i8| x as int), 1) == a@[0] as int);
        } else {
            let prev = result[i - 1];
            let curr = a[i];
            let prod_int: int = (prev as int) * (curr as int);
            
            // Convert to i8 with wrapping overflow
            let next_val: i8 = if prod_int < -128 {
                ((prod_int + 128) % 256 - 128) as i8
            } else if prod_int > 127 {
                ((prod_int + 128) % 256 - 128) as i8
            } else {
                prod_int as i8
            };
            
            result.push(next_val);
            
            proof {
                let a_ints = a@.map(|_index, x: i8| x as int);
                product_prefix_lemma(a_ints, (i + 1) as int);
                assert(product_prefix(a_ints, (i + 1) as int) == product_prefix(a_ints, i as int) * a_ints[i as int]);
                assert(prev as int == result@[(i - 1) as int] as int);
                assert(result@[(i - 1) as int] as int == product_prefix(a_ints, i as int));
                assert(curr as int == a@[i as int] as int);
                assert(a@[i as int] as int == a_ints[i as int]);
                assert(next_val as int == prod_int);
                assert(prod_int == (prev as int) * (curr as int));
                assert(result@[i as int] as int == product_prefix(a_ints, (i + 1) as int));
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}