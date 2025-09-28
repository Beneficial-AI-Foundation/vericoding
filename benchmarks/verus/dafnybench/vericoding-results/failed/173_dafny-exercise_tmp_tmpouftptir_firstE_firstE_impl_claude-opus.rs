use vstd::prelude::*;

verus! {

// <vc-helpers>

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
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a@[j] != 'e',
        decreases
            a.len() - i,
    {
        if a[i] == 'e' {
            assert(a@[i as int] == 'e');
            assert(forall|j: int| 0 <= j < i ==> a@[j] != 'e');
            assert(0 <= i < a.len());
            return i as i32;
        }
        i += 1;
    }
    assert(i == a.len());
    assert(forall|j: int| 0 <= j < a.len() ==> a@[j] != 'e');
    assert(!a@.contains('e') by {
        assert forall|j: int| 0 <= j < a@.len() implies a@[j] != 'e' by {
            assert(a@[j] != 'e');
        }
    });
    -1
}
// </vc-code>

fn main() {
}

}