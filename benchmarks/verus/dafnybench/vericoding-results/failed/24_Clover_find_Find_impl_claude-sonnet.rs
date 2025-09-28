use vstd::prelude::*;

verus! {

// <vc-helpers>
fn lemma_cast_bounds(a: &[i32], i: usize)
    requires 0 <= i < a.len(), a.len() <= i32::MAX as usize
    ensures 0 <= i as i32 < a.len() as i32
{
}
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
    if a.len() > i32::MAX as usize {
        return -1;
    }
    
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a[j] != key,
            a.len() <= i32::MAX as usize,
        decreases a.len() - i,
    {
        if a[i] == key {
            assert(i < a.len());
            assert(0 <= i as i32 < a.len() as i32);
            assert(a[i as int] == key);
            assert(forall|j: int| 0 <= j < i as int ==> a[j] != key);
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