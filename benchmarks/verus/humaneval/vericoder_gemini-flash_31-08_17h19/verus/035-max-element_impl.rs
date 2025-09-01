use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    // impl-start
    let mut max: i32 = a[0];
    let mut i: usize = 1;

    #[verifier::loop_invariant_when(
        i <= a.len(),
        forall|j: int| 0 <= j < i as int ==> a[j] <= max,
        exists|j: int| 0 <= j < i as int && a[j] == max,
    )]
    while (i < a.len())
    {
        if a[i] > max {
            max = a[i];
        } else {
            // Need to prove that max remains the maximum of `a[0..i]`
            // and that `max` is still one of the elements
            proof {
                assert(forall|j: int| 0 <= j < (i + 1) as int ==> a[j] <= max);
                assert(exists|j: int| 0 <= j < (i + 1) as int && a[j] == max);
            }
        }
        i = i + 1;
    }
    max
    // impl-end
}
// </vc-code>

fn main() {}
}