use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn within_i32_range(x: int) -> bool {
    x <= 2147483647 && x >= -2147483648
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn find(a: &[i32], key: i32) -> (index: i32)
    ensures
        -1 <= index < a.len() as i32,
        index != -1 ==> a[index as int] == key && (forall|i: int| 0 <= i < index ==> a[i] != key),
        index == -1 ==> (forall|i: int| 0 <= i < a.len() ==> a[i] != key),
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a[j] != key,
            i <= 2147483647,
        decreases a.len() - i,
    {
        if a[i] == key {
            assert(a[i as int] == key);
            assert(forall|j: int| 0 <= j < i ==> a[j] != key);
            assert(0 <= i < a.len());
            assert(i <= 2147483647);
            return i as i32;
        }
        i += 1;
    }
    assert(forall|j: int| 0 <= j < a.len() ==> a[j] != key);
    -1
}
// </vc-code>

fn main() {}

}