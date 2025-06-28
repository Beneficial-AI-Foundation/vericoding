use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn firste(a: Vec<char>) -> (c: int)
    ensures
        -1 <= c < a.len(),
        0 <= c < a.len() ==> a.spec_index(c as int) == 'e' && forall|x: int| 0 <= x < c ==> a.spec_index(x) != 'e',
        c == -1 ==> forall|x: int| 0 <= x < a.len() ==> a.spec_index(x) != 'e'
{
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            forall|x: int| 0 <= x < i ==> a.spec_index(x) != 'e'
    {
        if a[i] == 'e' {
            // Add proof that we found 'e' at position i
            assert(a.spec_index(i as int) == 'e');
            // The invariant ensures no 'e' before position i
            assert(forall|x: int| 0 <= x < i ==> a.spec_index(x) != 'e');
            return i as int;
        }
        i = i + 1;
    }
    
    // When we exit the loop, i == a.len() and we haven't found 'e'
    // The invariant tells us there's no 'e' in positions 0..i
    // Since i == a.len(), there's no 'e' in the entire vector
    assert(i == a.len());
    assert(forall|x: int| 0 <= x < a.len() ==> a.spec_index(x) != 'e');
    return -1;
}

}