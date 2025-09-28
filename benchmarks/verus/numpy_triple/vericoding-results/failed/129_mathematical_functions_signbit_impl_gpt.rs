// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_negative(x: f32) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): build spec sequence mapping is_negative over a Seq<f32> */
spec fn sign_seq(x: Seq<f32>) -> Seq<bool>
{
    Seq::new(x.len(), |i: int| is_negative(x[i]))
}
// </vc-helpers>

// <vc-spec>
fn signbit(x: Vec<f32>) -> (result: Vec<bool>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == is_negative(x[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build result via loop and maintain invariant tying to spec is_negative */
    let n: usize = x.len();
    let mut r: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == x.len(),
            (n as int) == x@.len(),
            i <= n,
            r.len() == i,
            forall|j: int| 0 <= j < i as int ==> r@[j] == is_negative(x@[j]),
        decreases (n - i) as int
    {
        let xi = x[i];
        let b: bool = is_negative(xi);
        r.push(b);
        i += 1;
    }
    r
}
// </vc-code>


}
fn main() {}