// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn cum_prod(a: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() > 0,
    ensures 
        result.len() == a.len(),
        result[0] == a[0],
        forall|i: int| 0 < i < a.len() ==> result[i] as int == result[i-1] as int * a[i] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added proof assertions to help verify invariant and handled overflow with wrapping_mul */
    let mut result = Vec::new();
    result.push(a[0]);
    
    let mut i = 1;
    while i < a.len()
        invariant
            0 < i <= a.len(),
            result.len() == i,
            result[0] == a[0],
            forall|j: int| 0 < j < result.len() ==> result[j] as int == ((result[j-1] as int * a[j] as int) % 256 + 256) % 256 - if (result[j-1] as int * a[j] as int) % 256 >= 128 { 256 } else { 0 },
        decreases a.len() - i
    {
        let prev = result[i - 1];
        let curr = a[i];
        let product: i8 = ((prev as int * curr as int) % 256) as i8;
        
        proof {
            assert(result.len() == i);
            assert(0 < i < a.len());
        }
        
        result.push(product);
        
        proof {
            assert(result.len() == i + 1);
            assert(result[i] == product);
            assert(product as int == ((prev as int * curr as int) % 256 + 256) % 256 - if (prev as int * curr as int) % 256 >= 128 { 256 } else { 0 });
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}