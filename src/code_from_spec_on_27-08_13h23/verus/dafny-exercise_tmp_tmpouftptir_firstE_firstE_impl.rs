use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper function to check if a character is 'e'
pub fn is_e(c: char) -> bool {
    c == 'e'
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
fn firstE(a: &[char]) -> (x: i32)
    ensures
        if a@.contains('e') {
            0 <= x < a@.len() as int && a@[x as int] == 'e' && 
            forall|i: int| 0 <= i < x ==> a@[i] != 'e'
        } else {
            x == -1
        }
{
    let mut i: i32 = 0;
    while i < a@.len() as i32
        invariant
            0 <= i <= a@.len() as i32,
            forall|j: int| 0 <= j < i ==> a@[j] != 'e'
    {
        if a@[i as int] == 'e' {
            return i;
        }
        i = i + 1;
    }
    return -1;
}
// </vc-code>

fn main() {
}

}