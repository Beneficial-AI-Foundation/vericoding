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
    let ghost mut max_val = a.spec_index(0);
    let mut i = 1;
    
    while i < x
        invariant
            1 <= i <= x,
            forall|j: int| 0 <= j < i ==> a.spec_index(j) <= max_val,
            exists|j: int| 0 <= j < i && a.spec_index(j) == max_val,
    {
        if a.spec_index(i) > max_val {
            max_val = a.spec_index(i);
        }
        i = i + 1;
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
        if a.spec_index(pos) > max_val {
            break;
        }
        pos = pos + 1;
    }
    
    // Prove postconditions
    assert(x <= pos < a.len());
    assert(forall|i: int| 0<=i<x ==> a.spec_index(i)<=max_val);
    assert(exists|i: int| 0<=i<x && a.spec_index(i)==max_val);
    
    // Prove the fourth postcondition: if pos < a.len()-1, then a[pos] > max_val
    if x <= pos < a.len() - 1 {
        // We exited the loop early due to break, so a[pos] > max_val
        assert(a.spec_index(pos) > max_val);
        // For any i < pos, we have a[i] <= max_val < a[pos]
        assert(forall|i: int| 0 <= i < pos ==> {
            if i < x {
                a.spec_index(i) <= max_val && max_val < a.spec_index(pos)
            } else {
                a.spec_index(i) <= max_val && max_val < a.spec_index(pos)
            }
        });
        assert(forall|i: int| 0<=i<p ==> a.spec_index(i) < a.spec_index(pos));
    }
    
    // Prove the fifth postcondition
    if forall|i: int| x<=i<a.len() && a.spec_index(i)<=max_val {
        // If all elements from x onwards are <= max_val, then pos must be a.len()-1
        assert(pos == a.len() - 1);
    }
    
    (max_val, pos)
}

}