use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
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
    while i < n {
        invariant 0 <= i && i <= n;
        invariant forall|k: int| 0 <= k < i ==> #[trigger] a[k as usize] == v;
        if a[i as usize] != v {
            proof {
                // witness that 0 and i are two indices with differing values
                assert(a[0] == v);
                assert(a[i as usize] != v);
                assert(a[0] != a[i as usize]);
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
        i = i + 1;
    }
    true
}
// </vc-code>

fn main() {}
}