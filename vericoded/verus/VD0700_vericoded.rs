use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn all_elements_equal(a: &[i32], n: i32) -> (result: bool)
    ensures
        result ==> forall|i: int| 0 <= i < a.len() ==> a[i] == n,
        !result ==> exists|i: int| 0 <= i < a.len() && a[i] != n,
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i as int,
            i as int <= a.len() as int,
            forall|j: int| 0 <= j && j < i as int ==> #[trigger] a[j] == n
        decreases a.len() - i
    {
        if a[i] != n {
            proof {
                let k = i as int;
                assert(0 <= k && k < a.len() as int);
                assert(a[k] != n);
                assert(exists|t: int| 0 <= t && t < a.len() as int && #[trigger] a[t] != n) by {
                    let t = k;
                    assert(0 <= t && t < a.len() as int && a[t] != n);
                }
            }
            return false;
        }
        i += 1;
    }
    proof {
        assert(i as int == a.len() as int);
        assert(forall|j: int| 0 <= j && j < a.len() as int ==> #[trigger] a[j] == n);
    }
    true
}
// </vc-code>

fn main() {
}

}