use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ArraySum(a: Vec<int>, b: Vec<int>) -> (c: Vec<int>)
    requires
        a.len() == b.len()
    ensures
        c.len() == a.len() && 
        forall|i: int| 0 <= i < c.len() ==> c.spec_index(i) == a.spec_index(i) + b.spec_index(i)
{
    let mut c = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            c.len() == i,
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> c.spec_index(j) == a.spec_index(j) + b.spec_index(j)
    {
        c.push(a[i] + b[i]);
        i = i + 1;
    }
    
    c
}

}