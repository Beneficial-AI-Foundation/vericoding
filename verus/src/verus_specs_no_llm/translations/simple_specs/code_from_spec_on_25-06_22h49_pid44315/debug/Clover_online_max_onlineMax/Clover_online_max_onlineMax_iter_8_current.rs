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
            break;
        }
        pos = pos + 1;
    }
    
    // If we didn't find any element > max_val, set pos to a.len()-1
    if pos == a.len() {
        pos = a.len() - 1;
    }
    
    // Prove postconditions
    assert(x <= pos < a.len());
    assert(forall|i: int| 0<=i<x ==> a.spec_index(i)<=max_val);
    assert(exists|i: int| 0<=i<x && a.spec_index(i)==max_val);
    
    // For fourth postcondition: if pos < a.len()-1, then a[pos] > max_val
    // and all elements from 0 to pos-1 are < a[pos]
    if pos < a.len() - 1 {
        // pos must have broken out of the loop, so a[pos] > max_val
        assert(a.spec_index(pos) > max_val);
        // All elements before pos (both in [0,x) and [x,pos)) are <= max_val < a[pos]
        assert(forall|i: int| 0<=i<pos ==> a.spec_index(i) <= max_val);
        assert(forall|i: int| 0<=i<pos ==> a.spec_index(i) < a.spec_index(pos));
    }
    
    // For fifth postcondition: if all elements from x onwards are <= max_val,
    // then we never found an element > max_val, so pos == a.len()-1
    assert(forall|i: int| x<=i<a.len() && a.spec_index(i)<=max_val ==> {
        // If all elements from x to end are <= max_val, the loop completed without breaking
        pos == a.len() - 1
    });
    
    (max_val, pos)
}

}