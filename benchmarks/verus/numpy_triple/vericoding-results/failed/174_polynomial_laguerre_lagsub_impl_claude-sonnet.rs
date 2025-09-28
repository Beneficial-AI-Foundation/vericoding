// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add cast and range helper for safe arithmetic */
fn safe_subtract_i8(a: i8, b: i8) -> (result: i8)
    requires a as int - b as int >= -128 && a as int - b as int <= 127,
    ensures result as int == a as int - b as int,
{
    a - b
}
// </vc-helpers>

// <vc-spec>
fn lagsub(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    requires c1.len() == c2.len(),
    ensures 
        result.len() == c1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == c1[i] as int - c2[i] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix bounds checking and cast safety */
    let mut result = Vec::new();
    let mut i = 0;
    while i < c1.len()
        invariant
            i <= c1.len(),
            result.len() == i,
            c1.len() == c2.len(),
            forall|j: int| 0 <= j < i ==> result@[j] as int == c1@[j] as int - c2@[j] as int,
        decreases c1.len() - i
    {
        proof {
            assert(i < c1.len());
            assert(c1.len() == c2.len());
            assert(i < c2.len());
        }
        
        let diff_val = safe_subtract_i8(c1[i], c2[i]);
        result.push(diff_val);
        
        proof {
            assert(result@[i as int] as int == c1@[i as int] as int - c2@[i as int] as int);
        }
        
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}