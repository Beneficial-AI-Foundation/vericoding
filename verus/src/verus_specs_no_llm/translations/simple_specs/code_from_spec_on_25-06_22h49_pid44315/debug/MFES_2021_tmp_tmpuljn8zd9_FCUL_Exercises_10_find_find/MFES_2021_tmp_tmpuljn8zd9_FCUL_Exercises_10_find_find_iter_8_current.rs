use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn find(a: Seq<int>, key: int) -> (index: int)
    requires
        a.len() > 0
    ensures
        0 <= index <= a.len(),
        index < a.len() ==> a.spec_index(index) == key
{
    let mut i: int = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall |j: int| 0 <= j < i ==> a.spec_index(j) != key
        decreases a.len() - i
    {
        if a[i as nat] == key {
            return i;
        }
        i = i + 1;
    }
    
    return a.len();
}

}