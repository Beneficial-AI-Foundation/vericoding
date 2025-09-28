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
        invariant 0 <= i <= a.len()
        invariant forall|j: int| 0 <= j < i ==> #[trigger] a[j] != key
    {
        if a[i] == key {
            return i as i32;
        }
        i += 1;
    }
    return -1;
}
// </vc-code>

fn main() {}

}