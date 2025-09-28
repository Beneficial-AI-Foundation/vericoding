use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn find(a: &[i32], key: i32) -> (index: i32)
    ensures
        -1 <= index < a.len() as i32,
        index != -1 ==> a[index as int] == key && (forall|i: int| 0 <= i < index ==> a[i] != key),
        index == -1 ==> (forall|i: int| 0 <= i < a.len() ==> a[i] != key),
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a[j] != key,
        decreases a.len() - i,
    {
        if a[i] == key {
            assert(i < a.len());
            assert(a[i as int] == key);
            assert(forall|j: int| 0 <= j < i ==> a[j] != key);
            if i <= i32::MAX as usize {
                return i as i32;
            } else {
                // Found the key but index too large to represent as i32
                // Continue searching to satisfy postcondition
                i += 1;
                continue;
            }
        }
        i += 1;
    }
    assert(i == a.len());
    assert(forall|j: int| 0 <= j < a.len() ==> a[j] != key);
    -1
}
// </vc-code>

fn main() {}

}