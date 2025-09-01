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
            forall|k: int| 0 <= k && k < i as int ==> #[trigger] a[k as usize] <= a[best]
    {
        let ai: i32 = a[i];
        let old_best: usize = best;
        if ai > a[old_best] {
            best = i;
            proof {
                // a[old_best] < ai
                assert(a[old_best] < ai);
                // old invariant: forall k < i: a[k] <= a[old_best]
                assert(forall|k: int| 0 <= k && k < i as int ==> a[k as usize] <= a[old_best]);
                // For k < i: a[k] <= a[old_best] < ai = a[best]
                // For k == i: a[i] == ai == a[best]
                assert(forall|k: int| 0 <= k && k < (i as int) + 1 ==> a[k as usize] <= a[best]);
            }
        } else {
            proof {
                assert(!(ai > a[old_best]));
                assert(ai <= a[old_best]);
                // old invariant for k < i
                assert(forall|k: int| 0 <= k && k < i as int ==> a[k as usize] <= a[old_best]);
                // for k == i: a[i] = ai <= a[old_best]
                assert(forall|k: int| 0 <= k && k < (i as int) + 1 ==> a[k as usize] <= a[old_best]);
            }
        }
        i += 1;
    }
    best
    // impl-end
}
// </vc-code>

fn main() {}
}