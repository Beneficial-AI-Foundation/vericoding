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
        forall i::0<=i<x==> a.spec_index(i)<=m,
        exists i::0<=i<x && a.spec_index(i)==m,
        x<=p<a.len()-1 ==> (forall i::0<=i<p ==> a.spec_index(i)<a.spec_index(p)),
        (forall i::x<=i<a.len() && a.spec_index(i)<=m) ==> p==a.len()-1
{
    // Find maximum in prefix a[0..x]
    let ghost mut max_val = a[0];
    let mut i = 1;
    
    while i < x
        invariant
            1 <= i <= x,
            forall j :: 0 <= j < i ==> a.spec_index(j) <= max_val,
            exists j :: 0 <= j < i && a.spec_index(j) == max_val,
    {
        if a[i] > max_val {
            max_val = a[i];
        }
        i = i + 1;
    }
    
    // Find first position from x where a[p] > max_val, or return a.len()-1
    let mut pos = x;
    
    while pos < a.len() - 1
        invariant
            x <= pos < a.len(),
            forall j :: x <= j < pos ==> a.spec_index(j) <= max_val,
            forall j :: 0 <= j < x ==> a.spec_index(j) <= max_val,
            exists j :: 0 <= j < x && a.spec_index(j) == max_val,
    {
        if a[pos] > max_val {
            break;
        }
        pos = pos + 1;
    }
    
    (max_val, pos)
}

}