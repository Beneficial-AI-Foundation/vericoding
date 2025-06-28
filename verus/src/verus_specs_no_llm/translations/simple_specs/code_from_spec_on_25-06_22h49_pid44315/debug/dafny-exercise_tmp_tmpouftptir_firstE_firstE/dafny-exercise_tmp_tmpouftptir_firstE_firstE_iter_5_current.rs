use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn contains_e(a: Seq<char>) -> bool {
    exists|i: int| 0 <= i < a.len() && a[i] == 'e'
}

fn firstE(a: Vec<char>) -> (x: int)
    ensures
        if contains_e(a@) then 0 <= x < a.len() && a@[x] == 'e' && forall|i: int| 0 <= i < x ==> a@[i] != 'e' else x == -1
{
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a@[j] != 'e'
    {
        if a[i] == 'e' {
            assert(i < a.len());
            assert(a@[i as int] == 'e');
            assert(forall|j: int| 0 <= j < i ==> a@[j] != 'e');
            assert(contains_e(a@)) by {
                assert(0 <= i < a@.len() && a@[i as int] == 'e');
            }
            return i as int;
        }
        i += 1;
    }
    
    assert(i == a.len());
    assert(forall|j: int| 0 <= j < a.len() ==> a@[j] != 'e');
    assert(!contains_e(a@)) by {
        if contains_e(a@) {
            let k = choose|k: int| 0 <= k < a@.len() && a@[k] == 'e';
            assert(0 <= k < a@.len());
            assert(0 <= k < a.len());
            assert(a@[k] != 'e');
            assert(a@[k] == 'e');
            assert(false);
        }
    }
    return -1;
}

}