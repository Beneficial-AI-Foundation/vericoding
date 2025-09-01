use vstd::prelude::*;

verus! {

// <vc-helpers>
fn distinct_elements_in_range(a: &[i32], lo: int, hi: int, v: i32) -> (result: bool)
    requires
        0 <= lo <= hi <= a.len(),
    ensures
        result ==> forall|k: int| lo <= k < hi ==> a[k] == v,
        !result ==> exists|k: int| lo <= k < hi && a[k] != v,
{
    if lo == hi {
        true
    } else {
        let mut i = lo;
        let mut found_distinct = false;
        while i < hi
            invariant
                lo <= i <= hi,
                !found_distinct ==> forall|k: int| lo <= k < i ==> a[k] == v,
        {
            if a[i] != v {
                found_distinct = true;
                break;
            }
            i = i + 1;
        }
        !found_distinct
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
    let n = a.len();

    if n == 0 {
        // An empty array trivially has only one distinct element (or zero, which counts).
        // The postcondition holds vacuously for the `result ==> ...` part.
        // For `!result ==> ...` part, it's impossible to find i, j, so !result must be false.
        // Thus, result must be true.
        true
    } else {
        let first_element = a[0];
        let mut i = 1;
        let mut all_same = true;

        while i < n
            invariant
                0 < n,
                1 <= i <= n,
                all_same ==> forall|j: int| 0 <= j < i ==> a[j] == first_element,
        {
            if a[i] != first_element {
                all_same = false;
                break;
            }
            i = i + 1;
        }
        all_same
    }
}
// </vc-code>

fn main() {}
}