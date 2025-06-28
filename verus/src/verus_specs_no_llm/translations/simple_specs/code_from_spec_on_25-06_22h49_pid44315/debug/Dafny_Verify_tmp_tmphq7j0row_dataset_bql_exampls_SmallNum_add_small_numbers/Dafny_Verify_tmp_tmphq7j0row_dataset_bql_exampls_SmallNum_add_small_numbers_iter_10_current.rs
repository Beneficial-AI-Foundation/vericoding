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
    let mut sum = 0int;
    let mut i = 0int;
    
    while i < n
        invariant
            0 <= i <= n,
            n <= a.len(),
            sum <= max * i,
            (forall j: int :: 0 <= j && j < n ==> a.spec_index(j) <= max)
    {
        // Use regular indexing for executable code
        let current = a[i as usize];
        
        // Assert that current equals spec_index for verification
        assert(current == a.spec_index(i));
        
        // Current is bounded by max due to precondition
        assert(current <= max);
        
        // Update sum
        sum = sum + current;
        
        // Prove the invariant is maintained
        assert(sum <= max * i + max);
        assert(max * i + max == max * (i + 1));
        
        i = i + 1;
    }
    
    // Post-loop: i == n, so sum <= max * i == max * n
    sum
}

}