use vstd::prelude::*;

verus! {

// <vc-helpers>
fn max_helper(a: &Vec<i32>, i: usize, current_max: i32) -> (max: i32)
    requires
        a.len() > 0,
        i <= a.len(),
    ensures
        forall|j: usize| i <= j < a.len() ==> a[j] <= max,
        (exists|j: usize| i <= j < a.len() && a[j] == max) || (i == a.len() && max == current_max),
    decreases a.len() - i
{
    if i == a.len() {
        current_max
    } else {
        let new_max = if a[i] > current_max { a[i] } else { current_max };
        let result = max_helper(a, i + 1, new_max);
        proof {
            assert(forall|j: usize| (i + 1) <= j < a.len() ==> a[j] <= result);
            if a[i] > current_max {
                assert(exists|j: usize| i <= j < a.len() && a[j] == new_max);
            } else {
                assert(exists|j: usize| i <= j < a.len() && a[j] == result);
            }
        }
        result
    }
}
// </vc-helpers>

// <vc-spec>
fn max_element(a: &Vec<i32>) -> (max: i32)
    // pre-conditions-start
    requires
        a.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int| 0 <= i < a.len() ==> a[i] <= max,
        exists|i: int| 0 <= i < a.len() && a[i] == max,
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    max_helper(a, 0, a[0])
}
// </vc-code>

}
fn main() {}