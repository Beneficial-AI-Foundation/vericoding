// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn remove_front(a: Vec<int>) -> (c: Vec<int>)
    requires
        a.len() > 0
    ensures
        a.spec_index(1..) == c.spec_index(..)
{
    let mut c = Vec::new();
    let mut i = 1;
    
    while i < a.len()
        invariant
            i <= a.len(),
            c.len() == i - 1,
            forall|j: int| 0 <= j < c.len() ==> c[j] == a[j + 1]
    {
        c.push(a[i]);
        i += 1;
    }
    
    assert(c.spec_index(..) =~= a.spec_index(1..));
    c
}

}