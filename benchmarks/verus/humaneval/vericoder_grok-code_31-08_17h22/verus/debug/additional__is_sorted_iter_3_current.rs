use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn is_sorted(lst: &[i32]) -> (result: bool)
    // pre-conditions-start
    requires
        lst.len() >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result <== forall|i: int, j: int| 0 <= i && i < j && j < lst.len() ==> lst[i] <= lst[j],
        !result ==> exists|i: int, j: int| 0 <= i && i < j && j < lst.len() && lst[i] > lst[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let len: usize = lst.len();
    while i < len - 1
        invariant
            0 <= i < len,
            forall|k: int| 0 <= k < i ==> #[trigger] (lst@[k] <= lst@[k+1])
        decreases (len as int - i as int)
    {
        if lst[i] > lst[i + 1] {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

fn main() {}
}