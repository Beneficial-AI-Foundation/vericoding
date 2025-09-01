use vstd::prelude::*;

verus! {

// <vc-helpers>
fn find_diff(a: &[i32], i: int) -> Option<(int, int)>
    requires 0 <= i && i <= (a.len() as int)
    ensures match result {
        None => forall|k: int| 0 <= k && k < i ==>
                    a[k as usize] == a[0],
        Some((x, y)) => 0 <= x && x < i && 0 <= y && y < i && a[x as usize] != a[y as usize]
    }
    decreases i
{
    if i <= 1 {
        return None;
    }

    let prev = find_diff(a, i - 1);
    match prev {
        None => {
            // all elements < i-1 equal to a[0]; check element i-1
            if a[(i - 1) as usize] != a[0] {
                return Some((0, i - 1));
            } else {
                return None;
            }
        }
        Some(pair) => {
            return Some(pair);
        }
    }
}
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
    let res = find_diff(a, n);
    match res {
        None => {
            // no differing pair found in prefix of length n => all equal
            return true;
        }
        Some((x, y)) => {
            proof {
                assert(0 <= x && x < n);
                assert(0 <= y && y < n);
                assert(a[x as usize] != a[y as usize]);
                assert(exists|i: int, j: int|
                    0 <= i && i < n &&
                    0 <= j && j < n &&
                    a[i as usize] != a[j as usize]
                );
            }
            return false;
        }
    }
    // impl-end
}
// </vc-code>

fn main() {}
}