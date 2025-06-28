use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ArraySplit(a: Vec<int>) -> (b: Vec<int>, c: Vec<int>)
    ensures
        fresh(b),
        fresh(c),
        a@ == b@ + c@,
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
            forall|j: int| 0 <= j < i ==> b[j] == a[j]
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
            forall|k: int| 0 <= k < j - mid ==> c[k] == a[mid + k]
    {
        c.push(a[j]);
        j += 1;
    }
    
    // Prove the concatenation property
    assert(b.len() == mid);
    assert(c.len() == a.len() - mid);
    assert(a.len() == b.len() + c.len());
    
    // Prove that b@ + c@ == a@
    assert forall|idx: int| 0 <= idx < a.len() implies {
        if idx < mid {
            (b@ + c@)[idx] == b@[idx] == a@[idx]
        } else {
            (b@ + c@)[idx] == c@[idx - mid] == a@[idx]
        }
    } by {
        if idx < mid {
            assert(b@[idx] == a@[idx]);
        } else {
            assert(c@[idx - mid] == a@[idx]);
        }
    };
    
    assert((b@ + c@).len() == b@.len() + c@.len() == a@.len());
    assert(b@ + c@ =~= a@);
    
    // Prove size constraints for non-trivial arrays
    if a.len() > 1 {
        assert(mid < a.len()); // Since mid = a.len() / 2 and a.len() > 1
        assert(b.len() == mid < a.len());
        assert(c.len() == a.len() - mid);
        // For integer division: if a.len() > 1, then a.len() - a.len()/2 < a.len()
        assert(a.len() - mid < a.len());
    }
    
    (b, c)
}

}