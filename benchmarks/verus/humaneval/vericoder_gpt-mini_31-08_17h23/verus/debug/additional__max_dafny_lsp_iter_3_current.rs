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
    let n: int = a.len() as int;
    let mut i: int = 1;
    let mut best: int = 0;
    while i < n
        invariant
            0 <= i,
            i <= n,
            0 <= best,
            best < n,
            forall|k: int| 0 <= k && k < i ==> #[trigger] a[k] <= a[best]
    {
        let ai: i32 = a[i];
        let old_best: int = best;
        if ai > a[old_best] {
            best = i;
            proof {
                assert(a[old_best] < ai);
                assert(forall|k: int| 0 <= k && k < i ==> a[k] <= a[old_best]);
                assert(forall|k: int| 0 <= k && k < i + 1 ==> a[k] <= a[best]);
            }
        } else {
            proof {
                assert(!(ai > a[old_best]));
                assert(ai <= a[old_best]);
                assert(forall|k: int| 0 <= k && k < i ==> a[k] <= a[old_best]);
                assert(forall|k: int| 0 <= k && k < i + 1 ==> a[k] <= a[old_best]);
            }
        }
        i += 1;
    }
    best as usize
    // impl-end
}
// </vc-code>

fn main() {}
}