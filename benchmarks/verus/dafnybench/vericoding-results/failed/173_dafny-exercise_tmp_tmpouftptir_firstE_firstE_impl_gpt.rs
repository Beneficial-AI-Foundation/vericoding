use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
fn firstE(a: &[char]) -> (x: i32)
    ensures
        if a@.contains('e') {
            0 <= x < a@.len() && a@[x as int] == 'e' && 
            forall|i: int| 0 <= i < x ==> a@[i] != 'e'
        } else {
            x == -1
        }
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i as int <= a@.len(),
            forall|j: int| 0 <= j && j < i as int ==> #[trigger] a@[j] != 'e'
    {
        if a[i] == 'e' {
            return i as i32;
        }
        i += 1;
    }
    -1
}
// </vc-code>

fn main() {
}

}