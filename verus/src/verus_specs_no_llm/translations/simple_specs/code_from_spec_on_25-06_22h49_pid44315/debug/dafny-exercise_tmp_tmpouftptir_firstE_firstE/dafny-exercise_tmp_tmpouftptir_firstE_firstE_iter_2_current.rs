use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn firstE(a: Vec<char>) -> (x: int)
    ensures
        if 'e' in a@ then 0 <= x < a.len() && a[x] == 'e' && forall|i: int| 0 <= i < x ==> a[i] != 'e' else x == -1
{
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a[j] != 'e'
    {
        if a[i] == 'e' {
            return i as int;
        }
        i += 1;
    }
    
    return -1;
}

}