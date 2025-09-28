use vstd::prelude::*;

verus! {

// <vc-helpers>
fn lemma_no_e_found(a: Seq<char>, len: usize)
    requires
        len == a.len(),
        forall|j: int| 0 <= j < len ==> a@[j] != 'e'
    ensures
        !a.contains('e')
{
    if a.contains('e') {
        let idx = choose|k: int| 0 <= k < a.len() && a@[k] == 'e';
        assert(0 <= idx < len);
        assert(a@[idx] != 'e');
        assert(false);
    }
}
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
    for i in 0..a.len()
        invariant
            forall|j: int| 0 <= j < i ==> a@[j] != 'e'
    {
        if a[i] == 'e' {
            assert(a@[i as int] == 'e');
            assert(forall|j: int| 0 <= j < i ==> a@[j] != 'e');
            assert(0 <= i < a.len());
            assert(i < usize::MAX);
            return i as i32;
        }
    }
    lemma_no_e_found(a@, a.len());
    assert(!a@.contains('e'));
    -1
}
// </vc-code>

fn main() {
}

}