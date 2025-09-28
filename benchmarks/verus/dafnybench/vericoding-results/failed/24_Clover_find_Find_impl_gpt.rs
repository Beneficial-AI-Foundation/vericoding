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
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            i as int <= n as int,
            forall|j: int| 0 <= j < i as int ==> #[trigger] a[j] != key
        decreases
            n as int - i as int
    {
        if a[i] == key {
            return i as i32;
        }
        i += 1;
    }
    -1
}
// </vc-code>

fn main() {}

}