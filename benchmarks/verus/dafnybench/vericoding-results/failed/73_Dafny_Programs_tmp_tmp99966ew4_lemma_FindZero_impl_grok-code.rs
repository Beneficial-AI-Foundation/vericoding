use vstd::prelude::*;

verus! {

// <vc-helpers>
// no additional helpers needed
// </vc-helpers>

// <vc-spec>
fn find_zero(a: &[i32]) -> (index: i32)
    requires
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] >= 0,
        forall|i: int| 0 < i < a.len() ==> #[trigger] a[i-1] - 1 <= a[i],
    ensures
        (index < 0 ==> forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] != 0),
        (0 <= index ==> index < a.len() && a[index as int] == 0),
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            forall|k: int| 0 <= k < i ==> #[trigger] (a@)[k] != 0
        decreases a.len() - i
    {
        if (a@)[i] == 0 {
            return #[verifier::truncate] (i as i32);
        }
        i += 1;
    }
    assert(forall|k: int| 0 <= k < a.len() ==> #[trigger] (a@)[k] != 0);
    return -1;
}
// </vc-code>

fn main() {}

}