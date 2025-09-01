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
    // impl-start
    let n: usize = a.len();
    let mut i: usize = 1;
    let mut best: usize = 0;
    while i < n
        invariant
            i <= n,
            best < n,
            forall|k: int| #[trigger] a[k as usize] 0 <= k && k < i as int ==> a[k as usize] <= a[best]
    {
        let ai: i32 = a[i];
        if ai > a[best] {
            // then new best = i; need to show forall k < i+1: a[k] <= a[i]
            proof {
                // from the branch condition
                assert(a[best] < ai);
                // and from the loop invariant
                assert(forall|k: int| 0 <= k && k < i as int ==> a[k as usize] <= a[best]);
                // For any k < i, a[k] <= a[best] < ai, so a[k] <= ai.
            }
            best = i;
        } else {
            // ai <= a[best], so extending the invariant to include k == i holds
            proof {
                assert(!(ai > a[best]));
                assert(ai <= a[best]);
                assert(forall|k: int| 0 <= k && k < i as int ==> a[k as usize] <= a[best]);
            }
        }
        i += 1;
    }
    // At loop exit i == n, so invariant gives forall k < n: a[k] <= a[best]
    best
    // impl-end
}
// </vc-code>

fn main() {}
}