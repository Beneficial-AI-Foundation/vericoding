use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn find(a: Vec<int>, key: int) -> (index: int)
    requires
        a.len() > 0
    ensures
        0 <= index <= a.len(),
        index < a.len() ==> a.spec_index(index) == key
{
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall |j: int| 0 <= j < i ==> a.spec_index(j) != key
    {
        if a.spec_index(i as int) == key {
            return i as int;
        }
        i = i + 1;
    }
    
    return a.len() as int;
}

}