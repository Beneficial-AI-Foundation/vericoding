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
    let mut i: usize = 1;
    let mut min_index: usize = 0;
    
    while i < n as usize
        invariant
            1 <= i <= n,
            i <= a.len(),
            0 <= min_index < i,
            min_index < a.len(),
            a.spec_index(min_index as int) == min_val,
            (forall j : int :: 0 <= j && j < i ==> a.spec_index(j) >= min_val)
    {
        if a[i] < min_val {
            min_val = a[i];
            min_index = i;
        }
        i = i + 1;
    }
    
    min_val
}

}