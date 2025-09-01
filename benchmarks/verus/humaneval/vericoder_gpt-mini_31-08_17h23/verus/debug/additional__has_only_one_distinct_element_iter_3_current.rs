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
    let n: int = a.len() as int;
    if n <= 1 {
        return true;
    }
    let mut i: int = 1;
    while i < n
        invariant { 0 <= i && i <= n }
        invariant { forall|k: int| 0 <= k && k < i ==> a[k as usize] == a[0] }
        decreases { n - i }
    {
        if a[i as usize] != a[0] {
            // provide witnesses 0 and i for the existential
            proof {
                let j_int: int = i;
                assert(0 <= 0 && 0 < n);
                assert(0 <= j_int && j_int < n);
                assert(a[0] != a[j_int as usize]);
                assert(exists|x: int, y: int|
                    x == 0 && y == j_int &&
                    0 <= x && x < n &&
                    0 <= y && y < n &&
                    a[x as usize] != a[y as usize]
                );
                assert(exists|x: int, y: int| 0 <= x && x < n && 0 <= y && y < n && a[x as usize] != a[y as usize]);
            }
            return false;
        }
        i += 1;
    }
    // now i == n and invariant gives all elements equal to a[0]
    proof {
        assert(i == n);
        assert(forall|k: int| 0 <= k && k < i ==> a[k as usize] == a[0]);
        assert(forall|k: int| 0 <= k && k < n ==>
            {
                assert(0 <= k && k < i);
                assert(a[k as usize] == a[0]);
                true
            }
        );
        assert(forall|x: int, y: int| 0 <= x && x < n && 0 <= y && y < n ==> a[x as usize] == a[y as usize]);
    }
    return true;
    // impl-end
}
// </vc-code>

fn main() {}
}