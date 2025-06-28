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
            // We found an element greater than max_val
            // Prove postconditions for early return case
            assert(x <= pos < a.len());
            assert(a.spec_index(pos) > max_val);
            
            // Prove fourth postcondition: if x <= pos < a.len()-1, then forall i: 0<=i<pos => a[i] < a[pos]
            assert(forall|k: int| 0 <= k < x ==> a.spec_index(k) <= max_val);
            assert(forall|k: int| x <= k < pos ==> a.spec_index(k) <= max_val);
            assert(forall|k: int| 0 <= k < pos ==> 
                if k < x then a.spec_index(k) <= max_val else a.spec_index(k) <= max_val);
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
    
    // Verify postconditions for the case where we return a.len()-1
    assert(x <= pos < a.len()) by {
        assert(x < a.len());
        assert(pos == a.len() - 1);
        assert(a.len() > 0);
    }
    
    // First two postconditions are maintained from loop invariants
    assert(forall|i: int| 0<=i<x ==> a.spec_index(i)<=max_val);
    assert(exists|i: int| 0<=i<x && a.spec_index(i)==max_val);
    
    // Fourth postcondition: x<=p<a.len()-1 ==> (forall|i: int| 0<=i<p ==> a.spec_index(i)<a.spec_index(p))
    // Since pos == a.len()-1, we have x <= pos < a.len()-1 is false when a.len() > 1
    // and the implication is vacuously true
    assert(!(x <= pos < a.len() - 1)) by {
        assert(pos == a.len() - 1);
        assert(!(a.len() - 1 < a.len() - 1));
    }
    
    // Fifth postcondition: we've proven that forall i: x<=i<a.len() => a[i] <= max_val
    // so the antecedent is true and pos == a.len()-1
    assert(forall|i: int| x<=i<a.len() && a.spec_index(i)<=max_val) by {
        assert(forall|i: int| x<=i<a.len() ==> a.spec_index(i)<=max_val);
        assert(forall|i: int| x<=i<a.len() ==> (a.spec_index(i)<=max_val));
    }
    assert((forall|i: int| x<=i<a.len() && a.spec_index(i)<=max_val) ==> pos==a.len()-1);
    
    (max_val, pos)
}

}