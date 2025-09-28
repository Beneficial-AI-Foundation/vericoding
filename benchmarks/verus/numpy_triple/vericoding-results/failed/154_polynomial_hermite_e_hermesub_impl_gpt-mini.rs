// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute max of two int values */
fn max_int(a: int, b: int) -> int { if a >= b { a } else { b } }
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
    /* code modified by LLM (iteration 5): use int indices for Seq indexing and proper casts */
    let len1: int = c1@.len() as int;
    let len2: int = c2@.len() as int;
    let max_len: int = if len1 >= len2 { len1 } else { len2 };
    let mut result: Vec<i8> = Vec::new();
    let mut i: int = 0;
    while i < max_len
        invariant
            result@.len() == i as nat,
            forall|j: int| 0 <= j < (result@.len() as int) ==> 
                #[trigger] result@[j] == (if j < len1 { c1@[j] } else { 0 }) - (if j < len2 { c2@[j] } else { 0 }),
        decreases max_len - i
    {
        let a: i8 = if i < len1 { c1@[i] } else { 0 };
        let b: i8 = if i < len2 { c2@[i] } else { 0 };
        result.push(a - b);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}