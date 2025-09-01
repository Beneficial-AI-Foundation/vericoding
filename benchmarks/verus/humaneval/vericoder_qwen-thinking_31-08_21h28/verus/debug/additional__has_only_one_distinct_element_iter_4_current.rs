use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    if a.len() == 0 {
        true
    } else {
        let mut i: nat = 1;
        while i < a.len() {
            invariant (forall j: int :: 1 <= j && j < i ==> #[trigger] (a[j] == a[0]))
            if a[i] != a[0] {
                return false;
            }
            i = i + 1;
        }
        true
    }
}
// </vc-code>

fn main() {}
}