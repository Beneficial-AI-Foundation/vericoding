// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): equate wrapping_sub with spec subtraction for i8 */
proof fn wrapping_sub_eq_spec(a: i8, b: i8)
    ensures
        a.wrapping_sub(b) == a - b,
{
}

// </vc-helpers>

// <vc-spec>
fn subtract(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result@[i] == x1@[i] - x2@[i],
        /* Sanity check: subtracting zero preserves the original value */
        forall|i: int| 0 <= i < result.len() && x2@[i] == 0 ==> result@[i] == x1@[i],
        /* Sanity check: subtracting a value from itself yields zero */
        forall|i: int| 0 <= i < result.len() && x1@[i] == x2@[i] ==> result@[i] == 0,
        /* Anti-commutativity property */
        forall|i: int| 0 <= i < result.len() ==> result@[i] == -(x2@[i] - x1@[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed index type mismatch in proofs and maintained loop invariant */
    let n = x1.len();
    let mut out: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            x1@.len() == n as int,
            x2@.len() == n as int,
            0 <= i as int <= n as int,
            out@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> out@[j] == x1@[j] - x2@[j],
        decreases n as int - i as int
    {
        let idx = i;
        let a = x1[idx];
        let b = x2[idx];
        let c: i8 = a.wrapping_sub(b);
        out.push(c);
        proof {
            let k = idx as int;
            assert(0 <= k && k < n as int);
            wrapping_sub_eq_spec(a, b);
            assert(c == a - b);
            assert(a == x1@[k]);
            assert(b == x2@[k]);
            assert(out@[k] == c);
            assert(out@[k] == x1@[k] - x2@[k]);
        }
        i = idx + 1;
    }
    out
}
// </vc-code>


}
fn main() {}