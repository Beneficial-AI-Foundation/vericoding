// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): return the maximum of two usize values */
fn max_usize(a: usize, b: usize) -> usize {
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
    /* code modified by LLM (iteration 5): implement legadd with safe get-based indexing and maintain loop invariant relating built prefix to specification */
    let len1 = c1.len();
    let len2 = c2.len();
    let mut result: Vec<i8> = Vec::new();
    let max = if len1 >= len2 { len1 } else { len2 };
    let mut i: usize = 0;
    while i < max
        invariant
            i <= max,
            result.len() == i,
            forall|k: int| 0 <= k < (i as int) ==> {
                let val1: int = if k < c1@.len() { c1@[k] as int } else { 0 };
                let val2: int = if k < c2@.len() { c2@[k] as int } else { 0 };
                result@[k] as int == val1 + val2
            },
        decreases max - i
    {
        let v1: i8 = match c1.get(i) { Some(v) => *v, None => 0 };
        let v2: i8 = match c2.get(i) { Some(v) => *v, None => 0 };
        let s: i16 = (v1 as i16) + (v2 as i16);
        let x: i8 = #[verifier::truncate] (s as i8);
        result.push(x);
        i = i + 1;
    }
    proof {
        assert(i == max);
        assert(result.len() == i);
        assert(forall|k: int| 0 <= k < (i as int) ==> {
            let val1: int = if k < c1@.len() { c1@[k] as int } else { 0 };
            let val2: int = if k < c2@.len() { c2@[k] as int } else { 0 };
            result@[k] as int == val1 + val2
        });
    }
    result
}
// </vc-code>


}
fn main() {}