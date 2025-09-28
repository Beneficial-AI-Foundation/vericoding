use vstd::prelude::*;

verus! {

// Predicate to check if array slice is sorted
spec fn sorted(a: &[int], l: int, u: int) -> bool {
    forall|i: int, j: int| 0 <= l <= i <= j <= u < a.len() ==> a[i] <= a[j]
}

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
fn binary_search(a: &[int], key: int) -> (index: i32)
    requires 
        a.len() > 0,
        sorted(a, 0, (a.len() - 1) as int),
    ensures 
        index >= 0 ==> index < a.len() && a[index as int] == key,
        index < 0 ==> forall|k: int| 0 <= k < a.len() ==> a[k] != key,
// </vc-spec>
// <vc-code>
{
    let mut i: int = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] a[k] != key,
        decreases a.len() - i
    {
        if a[i] == key {
            let idx: i32 = i as i32;
            return idx;
        }
        i = i + 1;
    }
    assert(i <= a.len());
    assert(!(i < a.len()));
    assert(i == a.len());
    assert(forall|k: int| 0 <= k < a.len() ==> a[k] != key);
    -1
}
// </vc-code>

fn main() {
}

}