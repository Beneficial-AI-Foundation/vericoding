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
    let mut result = true;
    let mut i: usize = 0;
    let s = lst@;
    while i < lst.len() - 1
        invariant
            0 <= i <= lst.len() - 1,
            result == forall |k: int, j: int| 0 <= k < j <= i ==> #[trigger] (s[k] <= s[j])
    {
        if !(lst[i] <= lst[i+1]) {
            result = false;
            break;
        }
        i += 1;
    }
}
// </vc-code>

fn main() {}
}