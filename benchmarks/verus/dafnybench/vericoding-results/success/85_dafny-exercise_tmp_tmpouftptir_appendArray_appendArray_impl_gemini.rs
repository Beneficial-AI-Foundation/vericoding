// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn append_array(a: &[i32], b: &[i32]) -> (c: Vec<i32>)
    ensures 
        c.len() == a.len() + b.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] == c[i],
        forall|i: int| 0 <= i < b.len() ==> b[i] == c[a.len() + i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fix compilation error using Vec::new and extend_from_slice */
    let mut c: Vec<i32> = Vec::new();
    c.extend_from_slice(a);
    c.extend_from_slice(b);
    c
}
// </vc-code>

}
fn main() {}