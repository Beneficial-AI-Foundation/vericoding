use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn max_dafny_lsp(a: &[i32]) -> (x: usize)
    // pre-conditions-start
    requires
        a.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= x < a.len(),
        forall|k: int| 0 <= k < a.len() ==> a[k] <= a[x as int],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut x = 0;
    let mut i = 1;
    while i < a.len()
        invariant
            0 <= x < i,
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] a@[k] <= a@[x as int],
    {
        if a[i] > a[x] {
            x = i;
        }
        i += 1;
    }
    x
}
// </vc-code>

fn main() {}
}