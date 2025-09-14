// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn max_dafny_lsp(a: &[i32]) -> (x: usize)
    requires
        a.len() > 0,
    ensures
        0 <= x < a.len(),
        forall|k: int| 0 <= k < a.len() ==> a[k] <= a[x as int],
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 1;
    let mut x: usize = 0;

    while i < a.len()
        invariant
            0 < i <= a.len(),
            0 <= x < i,
            forall|k: int| 0 <= k < i ==> a[k] <= a[x as int],
        decreases a.len() - i,
    {
        if a[i] > a[x] {
            x = i;
        }
        i = i + 1;
    }

    x
}
// </vc-code>

}
fn main() {}