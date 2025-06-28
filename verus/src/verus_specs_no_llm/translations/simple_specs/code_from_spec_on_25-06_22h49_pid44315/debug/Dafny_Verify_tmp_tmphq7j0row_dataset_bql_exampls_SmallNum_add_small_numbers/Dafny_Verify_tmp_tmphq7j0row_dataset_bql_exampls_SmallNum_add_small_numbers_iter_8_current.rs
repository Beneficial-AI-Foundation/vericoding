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
    
    // Ensure n can be safely cast to usize
    assert(n > 0);
    assert(n <= a.len());
    let n_usize = n as usize;
    
    while i < n_usize
        invariant
            0 <= i <= n_usize,
            n_usize == n,
            n <= a.len(),
            sum <= max * (i as int),
            (forall j: int :: 0 <= j && j < n ==> a.spec_index(j) <= max)
    {
        // Establish that i is within bounds
        assert(i < n_usize);
        assert(n_usize == n);
        assert(n <= a.len());
        assert((i as int) < n);
        assert((i as int) < a.len());
        
        // Get the current element
        let current = a[i];
        
        // Establish the relationship between indexing and spec_index
        assert(a[i] == a.spec_index(i as int));
        assert(current <= max);
        
        // Prove sum won't overflow and maintains bound
        let old_sum = sum;
        let old_i = i;
        sum = sum + current;
        
        // Arithmetic reasoning
        assert(old_sum <= max * (old_i as int));
        assert(current <= max);
        assert(sum == old_sum + current);
        
        // Handle the case where max might be negative
        if max >= 0 {
            assert(sum <= max * (old_i as int) + max);
            assert(max * (old_i as int) + max == max * ((old_i as int) + 1));
            assert(sum <= max * ((old_i as int) + 1));
        } else {
            // When max < 0, current <= max means current + old_sum <= max + old_sum
            // Since old_sum <= max * (old_i as int) and max < 0, we need to be careful
            assert(sum <= old_sum + max);
            assert(old_sum <= max * (old_i as int));
            // For negative max: max * (old_i as int) + max = max * ((old_i as int) + 1)
            assert(max * (old_i as int) + max == max * ((old_i as int) + 1));
            assert(sum <= max * ((old_i as int) + 1));
        }
        
        i = i + 1;
        
        // Verify invariant is maintained
        assert((i as int) == (old_i as int) + 1);
        assert(sum <= max * (i as int));
    }
    
    // Post-loop assertions
    assert(i == n_usize);
    assert(n_usize == n);
    assert((i as int) == n);
    assert(sum <= max * (i as int));
    assert(sum <= max * n);
    
    sum
}

}