use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let mut max_index = 0;
    let mut i = 1;
    while i < a.len()
        invariant max_index < i
        invariant (forall k: int :: 0 <= k < i ==> #[trigger(a[k as usize])] a[k as usize] <= a[max_index])
    {
        if a[i] > a[max_index] {
            max_index = i;
        }
        i = i + 1;
    }
    max_index
}
// </vc-code>

fn main() {}
}