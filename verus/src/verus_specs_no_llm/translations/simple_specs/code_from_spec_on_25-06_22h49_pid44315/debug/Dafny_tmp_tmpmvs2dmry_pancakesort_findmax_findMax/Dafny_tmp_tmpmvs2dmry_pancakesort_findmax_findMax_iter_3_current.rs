use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn findMax(a: Vec<int>, n: int) -> (r: int)
    requires
        a.len() > 0,
        0 < n <= a.len()
    ensures
        0 <= r < n <= a.len(),
        forall|k: int| 0 <= k < n ==> a.spec_index(r) >= a.spec_index(k),
{
    let mut max_idx: usize = 0;
    let mut i: usize = 1;
    let n_usize = n as usize;
    
    while i < n_usize
        invariant
            0 < n <= a.len(),
            n_usize == n as usize,
            1 <= i <= n_usize,
            0 <= max_idx < i,
            max_idx < a.len(),
            forall|k: int| 0 <= k < i ==> a.spec_index(max_idx as int) >= a.spec_index(k),
    {
        if a[i] > a[max_idx] {
            max_idx = i;
        }
        i += 1;
    }
    
    // Proof that max_idx satisfies the postcondition
    assert(max_idx < n_usize);
    assert(n_usize == n as usize);
    assert(max_idx as int < n);
    
    // Proof that max_idx is indeed the maximum over the range [0, n)
    assert(forall|k: int| 0 <= k < n ==> a.spec_index(max_idx as int) >= a.spec_index(k));
    
    max_idx as int
}

}