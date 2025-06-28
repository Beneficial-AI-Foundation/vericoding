use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn onlineMax(a: Vec<int>, x: int) -> (m: int, p: int)
    requires
        1<=x<a.len(),
        a.len()!=0
    ensures
        x<=p<a.len(),
        forall|i: int| 0<=i<x ==> a.spec_index(i)<=m,
        exists|i: int| 0<=i<x && a.spec_index(i)==m,
        x<=p<a.len()-1 ==> (forall|i: int| 0<=i<p ==> a.spec_index(i)<a.spec_index(p)),
        (forall|i: int| x<=i<a.len() && a.spec_index(i)<=m) ==> p==a.len()-1
{
    // Find maximum in prefix a[0..x]
    let mut max_val = a[0];
    let mut i = 1;
    
    while i < x
        invariant
            1 <= i <= x,
            forall|j: int| 0 <= j < i ==> a.spec_index(j) <= max_val,
            exists|j: int| 0 <= j < i && a.spec_index(j) == max_val,
        decreases x - i
    {
        if a[i] > max_val {
            max_val = a[i];
        }
        i = i + 1;
    }
    
    // Find first position from x where a[p] > max_val, or return a.len()-1
    let mut pos = x;
    
    while pos < a.len()
        invariant
            x <= pos <= a.len(),
            forall|j: int| x <= j < pos ==> a.spec_index(j) <= max_val,
            forall|j: int| 0 <= j < x ==> a.spec_index(j) <= max_val,
            exists|j: int| 0 <= j < x && a.spec_index(j) == max_val,
        decreases a.len() - pos
    {
        if a[pos] > max_val {
            // Prove that we'll satisfy the fourth postcondition
            assert(pos < a.len());
            assert(a.spec_index(pos) > max_val);
            assert(forall|k: int| 0 <= k < x ==> a.spec_index(k) <= max_val);
            assert(forall|k: int| x <= k < pos ==> a.spec_index(k) <= max_val);
            assert(forall|k: int| 0 <= k < pos ==> a.spec_index(k) <= max_val);
            assert(forall|k: int| 0 <= k < pos ==> a.spec_index(k) < a.spec_index(pos));
            return (max_val, pos);
        }
        pos = pos + 1;
    }
    
    // If we reach here, pos == a.len() and no element from x to end is > max_val
    assert(pos == a.len());
    assert(forall|j: int| x <= j < a.len() ==> a.spec_index(j) <= max_val);
    
    // Set pos to a.len()-1 as required
    pos = a.len() - 1;
    
    // Verify postconditions
    assert(x <= pos < a.len()) by {
        assert(x < a.len());
        assert(pos == a.len() - 1);
        assert(a.len() > 0);
    }
    
    assert(forall|i: int| 0<=i<x ==> a.spec_index(i)<=max_val);
    assert(exists|i: int| 0<=i<x && a.spec_index(i)==max_val);
    
    // For the fifth postcondition: we've proven that no element from x onwards is > max_val
    // so the implication holds
    assert((forall|i: int| x<=i<a.len() && a.spec_index(i)<=max_val) ==> pos==a.len()-1) by {
        assert(forall|i: int| x<=i<a.len() ==> a.spec_index(i)<=max_val);
        assert(pos == a.len() - 1);
    }
    
    (max_val, pos)
}

}