use vstd::prelude::*;

verus! {

// <vc-helpers>
// updated helpers (none needed)
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
            forall|k: usize| k < i ==> #[trigger] a[k] <= a[best]
    {
        let ai: i32 = a[i];
        let old_best: usize = best;
        if ai > a[old_best] {
            best = i;
            proof {
                // a[old_best] < ai
                assert(a[old_best] < ai);
                // inductive hypothesis
                assert(forall|k: usize| k < i ==> a[k] <= a[old_best]);
                // show property for i+1 with new best = i
                assert(forall|k: usize| k < i + 1 ==> a[k] <= a[best]);
            }
        } else {
            proof {
                assert(!(ai > a[old_best]));
                assert(ai <= a[old_best]);
                assert(forall|k: usize| k < i ==> a[k] <= a[old_best]);
                // best unchanged, so property holds for i+1
                assert(forall|k: usize| k < i + 1 ==> a[k] <= a[old_best]);
            }
        }
        i += 1;
    }
    proof {
        // at loop exit i == n
        assert(i == n);
        // from invariant we have forall k < n ...
        assert(forall|k: usize| k < n ==> a[k] <= a[best]);
        // translate to the required spec quantifier over int
        assert(forall|k: int| 0 <= k && k < n as int ==> a[k as usize] <= a[best]);
    }
    best
    // impl-end
}
// </vc-code>

fn main() {}
}