use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn firste(a: Vec<char>) -> (c: int)
    ensures
        c == -1 || (0 <= c < a.len()),
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
            assert(a.spec_index(i as int) == 'e');
            assert(forall|x: int| 0 <= x < i ==> a.spec_index(x) != 'e');
            assert(0 <= i < a.len());
            return (i as int);
        }
        i = i + 1;
    }
    
    assert(i == a.len());
    assert(forall|x: int| 0 <= x < i ==> a.spec_index(x) != 'e');
    assert(forall|x: int| 0 <= x < a.len() ==> a.spec_index(x) != 'e');
    return (-1);
}

}