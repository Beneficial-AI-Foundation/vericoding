use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
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
    assert(a@.len() <= i32::MAX);
    let mut idx: usize = 0;
    while idx < a.len()
        invariant
            forall|i: int| 0 <= i < (idx as int) ==> #[trigger] a@[i] != 'e'
        decreases (a@.len() - (idx as int))
    {
        if a[idx] == 'e' {
            return idx as i32;
        }
        idx += 1;
    }
    -1
}
// </vc-code>
// </vc-code>

fn main() {
}

}