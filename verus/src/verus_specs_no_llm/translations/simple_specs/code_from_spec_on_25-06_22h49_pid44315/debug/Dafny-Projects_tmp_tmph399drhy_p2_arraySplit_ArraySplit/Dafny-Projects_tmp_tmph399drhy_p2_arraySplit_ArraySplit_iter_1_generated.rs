use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ArraySplit(a: Vec<int>) -> (b: Vec<int>, c: Vec<int>)
    ensures
        fresh(b),
        fresh(c),
        a.spec_index(..) == b.spec_index(..) + c.spec_index(..),
        a.len() == b.len() + c.len(),
        a.len() > 1 ==> a.len() > b.len(),
        a.len() > 1 ==> a.len() > c.len()
{
    let mid = a.len() / 2;
    let mut b = Vec::new();
    let mut c = Vec::new();
    
    // Copy first half to b
    let mut i = 0;
    while i < mid
        invariant
            i <= mid,
            mid <= a.len(),
            b.len() == i,
            forall|j: int| 0 <= j < i ==> b.spec_index(j) == a.spec_index(j)
    {
        b.push(a[i]);
        i += 1;
    }
    
    // Copy second half to c
    let mut j = mid;
    while j < a.len()
        invariant
            mid <= j <= a.len(),
            c.len() == j - mid,
            forall|k: int| 0 <= k < j - mid ==> c.spec_index(k) == a.spec_index(mid + k)
    {
        c.push(a[j]);
        j += 1;
    }
    
    // Prove concatenation property
    assert(b.len() == mid);
    assert(c.len() == a.len() - mid);
    assert(a.len() == b.len() + c.len());
    
    // Prove size constraints for non-trivial arrays
    if a.len() > 1 {
        assert(mid < a.len()); // Since mid = a.len() / 2 and a.len() > 1
        assert(a.len() - mid <= a.len() / 2 + 1); // Integer division property
        assert(a.len() - mid < a.len()); // Since a.len() > 1
    }
    
    (b, c)
}

}