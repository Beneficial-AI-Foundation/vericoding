use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn firstE(a: Vec<char>) -> (x: int)
    ensures
        if 'e' in a.spec_index(..) then 0 <= x < a.len() && a.spec_index(x) == 'e' && forall i | 0 <= i < x :: a.spec_index(i) != 'e' else x == -1
{
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall j | 0 <= j < i :: a.spec_index(j) != 'e'
    {
        if a[i] == 'e' {
            return i as int;
        }
        i += 1;
    }
    
    return -1;
}

}