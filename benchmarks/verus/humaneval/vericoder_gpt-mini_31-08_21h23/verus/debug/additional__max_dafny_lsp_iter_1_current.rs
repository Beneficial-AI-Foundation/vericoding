use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
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
    let n = a.len();
    assert(n > 0);
    let mut i: usize = 1;
    let mut ans: usize = 0;
    while i < n
        invariant ans < n,
        invariant i <= n,
        invariant forall |k: int| 0 <= k && k < (i as int) ==> #[trigger] a[k] <= a[ans as int],
        decreases n - i
    {
        if a[i as int] > a[ans as int] {
            ans = i;
        }
        i = i + 1;
    }
    ans
}
// </vc-code>

fn main() {}
}