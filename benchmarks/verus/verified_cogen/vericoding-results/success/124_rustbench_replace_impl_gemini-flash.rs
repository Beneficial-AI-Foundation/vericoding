// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Removed placeholder helper definition */
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn replace(a: &mut Vec<i32>, x: i32, y: i32)
    ensures
        a.len() == old(a).len(),
        forall|k: int| 0 <= k < old(a).len() && old(a)[k] == x ==> a[k] == y,
        forall|k: int| 0 <= k < old(a).len() && old(a)[k] != x ==> a[k] == old(a)[k],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed compilation error by using `a[i]` for mutable vector access */
{
    let mut i = 0;
    while i < a.len()
        invariant
            a.len() == old(a).len(),
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i && old(a)@[k] == x ==> a@[k] == y,
            forall|k: int| 0 <= k < i && old(a)@[k] != x ==> a@[k] == old(a)@[k],
            forall|k: int| i <= k < old(a).len() ==> a@[k] == old(a)@[k],
        decreases a.len() - i
    {
        if a[i] == x {
            a.set(i, y);
        }
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}