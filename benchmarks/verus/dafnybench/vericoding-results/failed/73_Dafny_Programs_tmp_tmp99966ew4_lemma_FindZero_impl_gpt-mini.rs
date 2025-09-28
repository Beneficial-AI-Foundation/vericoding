use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// (no helpers needed)
 // </vc-helpers>
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
    while i < a.len() as usize
        invariant i <= a.len() as usize;
        invariant forall |j: usize| j < i ==> a[j] != 0;
        decreases (a.len() as usize - i)
    {
        if a[i] == 0 {
            return i as i32;
        }
        i += 1;
    }
    proof {
        assert(i >= a.len() as usize);
        assert(i <= a.len() as usize);
        assert(i == a.len() as usize);
        assert(forall |j: usize| j < a.len() as usize ==> a[j] != 0);
        assert(forall |k: int| 0 <= k < a.len() ==> a[k as usize] != 0);
    }
    -1
}
// </vc-code>

fn main() {}

}