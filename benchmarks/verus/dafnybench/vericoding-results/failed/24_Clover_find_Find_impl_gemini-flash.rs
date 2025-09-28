use vstd::prelude::*;

verus! {

// <vc-helpers>
fn eq_slice(a: &[i32], b: &[i32]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            forall |j: int| 0 <= j < i ==> a[j] == b[j],
        decreases a.len() - i
    {
        if a[i] != b[i] {
            return false;
        }
        i = i + 1;
    }
    true
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
    let mut i: i32 = 0;
    while (i as usize) < a.len()
        invariant
            0 <= i,
            i as usize <= a.len(),
            forall|j: int| 0 <= j < i ==> a[j] != key,
        decreases a.len() as int - i as int
    {
        if a[i as usize] == key {
            return i;
        }
        i = i + 1;
    }
    return -1;
}
// </vc-code>

fn main() {}

}