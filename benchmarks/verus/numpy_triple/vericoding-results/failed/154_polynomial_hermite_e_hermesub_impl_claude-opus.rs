// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    let max_len = if c1.len() >= c2.len() { c1.len() } else { c2.len() };
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    
    while i < max_len
        invariant
            i <= max_len,
            max_len == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                #[trigger] result@[j] == 
                (if j < c1@.len() { c1@[j] } else { 0 }) - 
                (if j < c2@.len() { c2@[j] } else { 0 }),
        decreases max_len - i
    {
        let val1: i8 = if i < c1.len() { c1[i] } else { 0 };
        let val2: i8 = if i < c2.len() { c2[i] } else { 0 };
        let diff: i8 = val1 - val2;
        result.push(diff);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}