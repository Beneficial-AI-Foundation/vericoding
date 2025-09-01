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
    // impl-start
    let n = a.len();
    if n <= 1 {
        return true;
    }
    let mut i: usize = 1;
    while i < n
        invariant { i <= n }
        invariant { forall|k: int| 0 <= k && k < i as int ==> a[k as usize] == a[0] }
    {
        if a[i] != a[0] {
            // provide witnesses 0 and i for the existential
            proof {
                let j_int: int = i as int;
                assert(0 <= 0 && 0 < n as int);
                assert(0 <= j_int && j_int < n as int);
                assert(a[0] != a[i]);
                assert(exists|x: int, y: int|
                    x == 0 && y == j_int &&
                    0 <= x && x < n as int &&
                    0 <= y && y < n as int &&
                    a[x as usize] != a[y as usize]
                );
                assert(exists|x: int, y: int| 0 <= x && x < n as int && 0 <= y && y < n as int && a[x as usize] != a[y as usize]);
            }
            return false;
        }
        i += 1;
    }
    // now i == n and invariant gives all elements equal to a[0]
    proof {
        assert(i == n);
        // from invariant: forall k < i ==> a[k]==a[0], and i==n, derive forall k < n ==> a[k]==a[0]
        assert(forall|k: int| 0 <= k && k < i as int ==> a[k as usize] == a[0]);
        assert(forall|k: int| 0 <= k && k < n as int ==>
            {
                assert(0 <= k && k < i as int);
                assert(a[k as usize] == a[0]);
                true
            }
        );
        // hence all pairs are equal
        assert(forall|x: int, y: int| 0 <= x && x < n as int && 0 <= y && y < n as int ==> a[x as usize] == a[y as usize]);
    }
    return true;
    // impl-end
}
// </vc-code>

fn main() {}
}