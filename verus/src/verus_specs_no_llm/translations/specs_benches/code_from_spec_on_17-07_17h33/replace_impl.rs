use vstd::prelude::*;

verus! {

//IMPL replace
#[verifier::loop_isolation(false)]
fn replace(a: &mut Vec<i32>, x: i32, y: i32)
    /* code modified by LLM (iteration 1): Fixed function signature and ensures clause placement */
    ensures
        a.len() == old(a).len(),
        forall|k: int| 0 <= k < old(a).len() && old(a)[k] == x ==> a[k] == y,
        forall|k: int| 0 <= k < old(a).len() && old(a)[k] != x ==> a[k] == old(a)[k],
{
    /* code modified by LLM (iteration 1): Removed invalid return statement and implemented proper loop body */
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == old(a).len(),
            forall|k: int| 0 <= k < i && old(a)[k] == x ==> a[k] == y,
            forall|k: int| 0 <= k < i && old(a)[k] != x ==> a[k] == old(a)[k],
            forall|k: int| i <= k < a.len() ==> a[k] == old(a)[k],
        /* code modified by LLM (iteration 2): Added decreases clause for termination */
        decreases a.len() - i
    {
        if a[i] == x {
            a.set(i, y);
        }
        i += 1;
    }
}

fn main() {}
}