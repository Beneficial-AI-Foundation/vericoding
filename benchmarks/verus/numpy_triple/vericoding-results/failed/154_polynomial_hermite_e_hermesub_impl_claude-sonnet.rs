// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma syntax by removing duplicate lemma keyword */
fn lemma_i8_subtraction_bounds(val1: i8, val2: i8)
    ensures
        -256 <= val1 as int - val2 as int <= 255,
        val1 as int - val2 as int >= i8::MIN as int,
        val1 as int - val2 as int <= i8::MAX as int
{
    assert(val1 >= i8::MIN && val1 <= i8::MAX);
    assert(val2 >= i8::MIN && val2 <= i8::MAX);
    assert(val1 as int >= -128 && val1 as int <= 127);
    assert(val2 as int >= -128 && val2 as int <= 127);
    assert(val1 as int - val2 as int >= -128 - 127);
    assert(val1 as int - val2 as int <= 127 - (-128));
}
// </vc-helpers>

// <vc-spec>
fn hermesub(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result@.len() ==> 
            #[trigger] result@[i] == 
            (if i < c1@.len() { c1@[i] } else { 0 }) - 
            (if i < c2@.len() { c2@[i] } else { 0 })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed index types by casting to int */
    let max_len = if c1.len() >= c2.len() { c1.len() } else { c2.len() };
    let mut result = Vec::with_capacity(max_len);
    
    let mut i = 0;
    while i < max_len
        invariant
            i <= max_len,
            result.len() == i,
            max_len == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
            forall|j: int| 0 <= j < result.len() ==> 
                #[trigger] result@[j] == 
                (if j < c1@.len() { c1@[j] } else { 0 }) - 
                (if j < c2@.len() { c2@[j] } else { 0 })
        decreases max_len - i
    {
        let val1 = if i < c1.len() { c1[i] } else { 0 };
        let val2 = if i < c2.len() { c2[i] } else { 0 };
        
        proof {
            lemma_i8_subtraction_bounds(val1, val2);
        }
        
        let diff = val1 - val2;
        
        result.push(diff);
        
        proof {
            assert(result@[i as int] == diff);
            assert(diff == (if i as int < c1@.len() { c1@[i as int] } else { 0 }) - 
                          (if i as int < c2@.len() { c2@[i as int] } else { 0 }));
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}