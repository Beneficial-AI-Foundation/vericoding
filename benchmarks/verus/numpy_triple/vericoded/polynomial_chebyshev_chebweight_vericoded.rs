// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): define endpoint predicate and a simple lemma using it */
spec fn is_endpoint(i: nat, n: nat) -> bool { i == 0 || i + 1 == n }

/* helper modified by LLM (iteration 2): trivial lemma showing the predicate implies the same bounds form */
proof fn lemma_is_endpoint_bounds(i: nat, n: nat)
    requires
        i < n,
    ensures
        is_endpoint(i, n) ==> (i == 0 || i + 1 == n),
{
    // Follows directly from the definition of is_endpoint
}

// </vc-helpers>

// <vc-spec>
fn chebweight(x: Vec<f32>) -> (result: Vec<f32>)
    requires 
        x.len() > 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use usize for executable indices and avoid ghost nat; fill weights with 0.5 at endpoints */
    let n: usize = x.len();
    let last: usize = n - 1;
    let mut w: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            w.len() == i,
            i <= n,
        decreases n as int - i as int
    {
        let val: f32 = if i == 0 || i == last { 0.5f32 } else { 1.0f32 };
        w.push(val);
        i = i + 1;
    }
    w
}
// </vc-code>

}
fn main() {}