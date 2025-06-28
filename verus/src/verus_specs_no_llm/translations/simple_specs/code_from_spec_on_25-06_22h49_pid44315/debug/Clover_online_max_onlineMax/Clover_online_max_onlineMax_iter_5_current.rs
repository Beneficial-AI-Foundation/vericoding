use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn onlineMax(a: Vec<int>, x: int) -> (ghost m: int, p: int)
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
    {
        if a[i] > max_val {
            max_val = a[i];
        }
        i = i + 1;
    }
    
    // At this point, max_val is the maximum of a[0..x]
    proof {
        assert(forall|j: int| 0 <= j < x ==> a.spec_index(j) <= max_val);
        assert(exists|j: int| 0 <= j < x && a.spec_index(j) == max_val);
    }
    
    // Find first position from x where a[p] > max_val, or return a.len()-1
    let mut pos = x;
    
    while pos < a.len() - 1
        invariant
            x <= pos < a.len(),
            forall|j: int| x <= j < pos ==> a.spec_index(j) <= max_val,
            forall|j: int| 0 <= j < x ==> a.spec_index(j) <= max_val,
            exists|j: int| 0 <= j < x && a.spec_index(j) == max_val,
    {
        if a[pos] > max_val {
            break;
        }
        pos = pos + 1;
    }
    
    // Establish the postconditions
    proof {
        assert(x <= pos < a.len());
        assert(forall|i: int| 0<=i<x ==> a.spec_index(i)<=max_val);
        assert(exists|i: int| 0<=i<x && a.spec_index(i)==max_val);
        
        // For the fourth postcondition: if pos < a.len()-1, then we broke early
        if pos < a.len() - 1 {
            // We must have broken because a[pos] > max_val
            assert(a.spec_index(pos) > max_val);
            // Therefore for any i < pos, if i < x then a[i] <= max_val < a[pos]
            // and if x <= i < pos then a[i] <= max_val (from loop invariant) < a[pos]
            assert(forall|i: int| 0<=i<pos ==> {
                if i < x {
                    a.spec_index(i) <= max_val && max_val < a.spec_index(pos)
                } else {
                    a.spec_index(i) <= max_val && max_val < a.spec_index(pos)
                }
            });
            assert(forall|i: int| 0<=i<pos ==> a.spec_index(i) < a.spec_index(pos));
        }
        
        // For the fifth postcondition: if all elements from x onwards are <= max_val,
        // then we never broke early and pos == a.len()-1
        if forall|i: int| x<=i<a.len() && a.spec_index(i)<=max_val {
            // Since we never found an element > max_val, pos must be a.len()-1
            // This follows from the loop condition and the assumption
            assert(forall|j: int| x <= j < a.len()-1 ==> a.spec_index(j) <= max_val);
            assert(pos == a.len() - 1);
        }
    }
    
    (max_val, pos)
}

}