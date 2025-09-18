// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): spec and exec xor helpers for clarity */
spec fn bool_xor_spec(a: bool, b: bool) -> bool { a != b }
fn bool_xor(a: bool, b: bool) -> bool { a != b }
// </vc-helpers>

// <vc-spec>
fn numpy_logical_xor(x1: Vec<bool>, x2: Vec<bool>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] != x2[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed int/nat indices and used ghost old view to reason about push */
    let n = x1.len();
    let mut out: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            out.len() == i,
            n == x1.len(),
            n == x2.len(),
            forall|j: int| 0 <= j < i as int ==> out@[j] == (x1@[j] != x2@[j])
        decreases n - i
    {
        let xi = x1[i];
        let yi = x2[i];
        let val = xi != yi;
        let ghost old_out = out@;
        out.push(val);
        proof {
            assert(out@ == old_out.push(val));
            assert(out@[i as int] == val);
        }
        i += 1;
    }
    out
}
// </vc-code>

}
fn main() {}