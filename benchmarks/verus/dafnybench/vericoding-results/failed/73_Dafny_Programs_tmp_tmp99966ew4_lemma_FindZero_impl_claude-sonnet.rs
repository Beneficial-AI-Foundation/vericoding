use vstd::prelude::*;

verus! {

// <vc-helpers>

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
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] a[j] != 0,
        decreases a.len() - i,
    {
        if a[i] == 0 {
            assert(i < a.len());
            assert(a[i as int] == 0);
            assert(i <= usize::MAX);
            assert(i as int >= 0);
            assert(i as int < a@.len());
            return i as i32;
        }
        i += 1;
    }
    assert(i == a.len());
    assert(forall|j: int| 0 <= j < a@.len() ==> #[trigger] a[j] != 0);
    -1
}
// </vc-code>

fn main() {}

}