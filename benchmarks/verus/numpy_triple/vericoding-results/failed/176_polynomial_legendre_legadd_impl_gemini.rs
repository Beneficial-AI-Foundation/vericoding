// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [no changes needed, helper is correct] */
fn max(a: usize, b: usize) -> (c: usize)
    ensures
        c == if a >= b { a } else { b },
{
    if a >= b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn legadd(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result@.len() == if c1@.len() >= c2@.len() { c1@.len() } else { c2@.len() },
        forall|i: int| 0 <= i < result@.len() ==> {
            let val1: int = if i < c1@.len() { c1@[i] as int } else { 0 };
            let val2: int = if i < c2@.len() { c2@[i] as int } else { 0 };
            #[trigger] result@[i] as int == val1 + val2
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [use executable integer types to fix compilation error] */
    let max_len = max(c1.len(), c2.len());
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < max_len
        invariant
            0 <= i <= max_len,
            max_len == max(c1.len(), c2.len()),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let val1: int = if j < c1@.len() { c1@[j] as int } else { 0 };
                let val2: int = if j < c2@.len() { c2@[j] as int } else { 0 };
                #[trigger] result@[j] as int == val1 + val2
            },
        decreases max_len - i
    {
        let val1 = if i < c1.len() { c1[i] } else { 0i8 };
        let val2 = if i < c2.len() { c2[i] } else { 0i8 };

        let sum = (val1 as i16) + (val2 as i16);
        
        result.push(sum as i8);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}