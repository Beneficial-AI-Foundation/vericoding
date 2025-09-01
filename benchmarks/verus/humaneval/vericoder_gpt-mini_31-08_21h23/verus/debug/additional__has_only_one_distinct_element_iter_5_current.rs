use vstd::prelude::*;

verus! {

// <vc-helpers>
// kept intentionally empty
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn has_only_one_distinct_element(a: &[i32]) -> (result: bool)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures
        result ==> forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j],
        !result ==> exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a[i] != a[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n: int = a.len() as int;
    if n <= 1 {
        return true;
    }
    let v: i32 = a[0];
    let mut i: int = 1;
    proof {
        // establish the loop invariants initially for i = 1
        assert(0 <= i && i <= n);
        assert(a[0usize] == v);
        assert(forall|k: int| 0 <= k && k < i ==> #[trigger] a[k as usize] == v);
    }
    while i < n
        invariant 0 <= i && i <= n;
        invariant forall|k: int| 0 <= k && k < i ==> #[trigger] (a[k as usize] == v);
        decreases n - i
    {
        if a[i as usize] != v {
            proof {
                assert(a[0usize] == v);
                assert(a[i as usize] != v);
                assert(a[0usize] != a[i as usize]);
                assert(exists|ii: int, jj: int|
                    ii == 0 &&
                    jj == i &&
                    0 <= ii && ii < n &&
                    0 <= jj && jj < n &&
                    a[ii as usize] != a[jj as usize]
                );
            }
            return false;
        }
        proof {
            // preserve the forall invariant for i+1
            assert(forall|k: int| 0 <= k && k < i ==> #[trigger] (a[k as usize] == v));
            // from the branch we know a[i] == v
            assert(a[i as usize] == v);
            // combine to get forall 0 <= k < i+1
            assert(forall|k: int| 0 <= k && k < i+1 ==> #[trigger] (a[k as usize] == v));
        }
        i = i + 1;
    }
    return true;
}
// </vc-code>

fn main() {}
}