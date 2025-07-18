use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn min(a: Vec<int>, n: int) -> (min: int)
    requires
        0 < n <= a.len()
    ensures
        (exists i : int :: 0 <= i && i < n && a.spec_index(i) == min),
        (forall i : int :: 0 <= i && i < n ==> a.spec_index(i) >= min)
{
    let mut min_val = a[0];
    let mut i = 1;
    
    while i < n
        invariant
            0 <= i <= n,
            (exists j : int :: 0 <= j && j < i && a.spec_index(j) == min_val),
            (forall j : int :: 0 <= j && j < i ==> a.spec_index(j) >= min_val)
    {
        if a[i as usize] < min_val {
            min_val = a[i as usize];
        }
        i = i + 1;
    }
    
    min_val
}

}