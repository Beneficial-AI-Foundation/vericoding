use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn add_small_numbers(a: Vec<int>, n: int, max: int) -> (r: int)
    requires
        n > 0,
        n <= a.len(),
        (forall i: int :: 0 <= i && i < n ==> a.spec_index(i) <= max)
    ensures
        r <= max * n
{
    let mut sum = 0;
    let mut i = 0;
    let n_usize = n as usize;
    
    while i < n_usize
        invariant
            0 <= i <= n_usize,
            n_usize == n,
            n <= a.len(),
            sum <= max * (i as int),
            (forall j: int :: 0 <= j && j < n ==> a.spec_index(j) <= max)
    {
        // Establish bounds for array access
        assert(i < n_usize);
        assert(n_usize == n);
        assert(n <= a.len());
        assert(i < a.len());
        
        // Get the current element and establish its bound
        let current = a[i];
        assert(a.spec_index(i as int) == current);
        assert(current <= max);
        
        // Update sum and establish new bound
        let old_sum = sum;
        sum = sum + current;
        
        // Prove the new sum bound
        assert(old_sum <= max * (i as int));
        assert(current <= max);
        assert(sum == old_sum + current);
        assert(sum <= max * (i as int) + max);
        assert(sum <= max * ((i as int) + 1));
        
        i = i + 1;
        
        // Maintain invariant
        assert(sum <= max * (i as int));
    }
    
    // Final assertions
    assert(i == n_usize);
    assert(n_usize == n);
    assert((i as int) == n);
    assert(sum <= max * n);
    
    sum
}

}