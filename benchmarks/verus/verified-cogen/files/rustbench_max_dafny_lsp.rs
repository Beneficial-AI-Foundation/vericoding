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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}