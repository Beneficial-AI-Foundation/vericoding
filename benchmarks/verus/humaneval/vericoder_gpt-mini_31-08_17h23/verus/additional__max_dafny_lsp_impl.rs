use vstd::prelude::*;

verus! {

// <vc-helpers>
// no changes needed in helpers for this proof
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
                // a[old_best] < ai
                assert(a[old_best] < ai);
                // inductive hypothesis: for all k < i, a[k] <= a[old_best]
                assert(forall|k: int| 0 <= k && k < i ==> a[k] <= a[old_best]);
                // show property for i+1 with new best = i
                assert(forall|k: int| 0 <= k && k < i + 1 ==> a[k] <= a[best]);
            }
        } else {
            proof {
                assert(!(ai > a[old_best]));
                assert(ai <= a[old_best]);
                assert(forall|k: int| 0 <= k && k < i ==> a[k] <= a[old_best]);
                // best unchanged, so property holds for i+1
                assert(forall|k: int| 0 <= k && k < i + 1 ==> a[k] <= a[old_best]);
            }
        }
        i += 1;
    }
    proof {
        // at loop exit i == n
        assert(i == n);
        // from invariant we have forall k < n ...
        assert(forall|k: int| 0 <= k && k < n ==> a[k] <= a[best]);
    }
    let res: usize = (best as int) as usize;
    proof {
        // ensure result in range
        assert(0 <= best && best < n);
        assert(res as int == best);
        // translate to the required spec quantifier over int
        assert(forall|k: int| 0 <= k && k < a.len() as int ==> a[k] <= a[res as int]);
    }
    res
    // impl-end
}
// </vc-code>

fn main() {}
}