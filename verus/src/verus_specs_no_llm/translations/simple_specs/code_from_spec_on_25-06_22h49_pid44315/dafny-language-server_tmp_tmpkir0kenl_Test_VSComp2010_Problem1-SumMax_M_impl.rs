use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn M(N: int, a: Vec<int>) -> (sum: int, max: int)
    requires
        0 <= N && a.len() == N && (forall k: int :: 0 <= k && k < N ==> 0 <= a.spec_index(k))
    ensures
        sum <= N * max
{
    if N == 0 {
        return (0, 0);
    }
    
    let mut sum: int = 0;
    let mut max: int = a[0];
    let mut i: usize = 0;
    let n_usize = N as usize;
    
    while i < n_usize
        invariant
            0 <= i <= n_usize,
            n_usize == N,
            0 <= sum,
            0 <= max,
            sum <= (i as int) * max,
            forall k: int :: 0 <= k < i ==> a.spec_index(k) <= max,
            sum == spec_sum(a, i as int),
            i > 0 ==> (exists k: int :: 0 <= k < i && a.spec_index(k) == max)
        decreases n_usize - i
    {
        let current = a[i];
        
        if current > max {
            // Update max first, then sum
            max = current;
            sum = sum + current;
            
            proof {
                // Prove the new invariant sum <= (i+1) * max
                assert(sum == spec_sum(a, i as int) + current);
                assert(max == current);
                assert(sum == spec_sum(a, i as int) + max);
                spec_sum_bound_with_new_max(a, i as int, max);
                assert(sum <= ((i as int) + 1) * max);
                
                // Prove the max existence invariant
                assert(a.spec_index(i as int) == max);
                assert(0 <= i as int < ((i as int) + 1));
            }
        } else {
            // Update sum, max stays the same
            sum = sum + current;
            
            proof {
                // max doesn't change, prove sum <= (i+1) * max
                assert(sum == spec_sum(a, i as int) + current);
                assert(current <= max);
                spec_sum_bound(a, i as int, max);
                assert(spec_sum(a, i as int) <= (i as int) * max);
                assert(sum <= (i as int) * max + max);
                assert(sum <= ((i as int) + 1) * max);
                
                // Prove the max existence invariant is preserved
                if i > 0 {
                    assert(exists k: int :: 0 <= k < i && a.spec_index(k) == max);
                }
            }
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i as int == N);
        assert(sum == spec_sum(a, N));
        assert(forall k: int :: 0 <= k < N ==> a.spec_index(k) <= max);
        spec_sum_bound(a, N, max);
    }
    
    (sum, max)
}

spec fn spec_sum(a: Vec<int>, n: int) -> int
    requires n >= 0, n <= a.len()
    decreases n
{
    if n <= 0 {
        0
    } else {
        spec_sum(a, n - 1) + a.spec_index(n - 1)
    }
}

proof fn spec_sum_bound(a: Vec<int>, n: int, bound: int)
    requires 
        n >= 0, 
        n <= a.len(),
        forall k: int :: 0 <= k < n ==> a.spec_index(k) <= bound
    ensures
        spec_sum(a, n) <= n * bound
    decreases n
{
    if n <= 0 {
        // Base case: spec_sum(a, 0) = 0 <= 0 * bound
    } else {
        // Inductive case
        spec_sum_bound(a, n - 1, bound);
        assert(spec_sum(a, n - 1) <= (n - 1) * bound);
        assert(a.spec_index(n - 1) <= bound);
        assert(spec_sum(a, n) == spec_sum(a, n - 1) + a.spec_index(n - 1));
        assert(spec_sum(a, n) <= (n - 1) * bound + bound);
        assert(spec_sum(a, n) <= n * bound);
    }
}

proof fn spec_sum_bound_with_new_max(a: Vec<int>, n: int, new_max: int)
    requires 
        n >= 0, 
        n <= a.len(),
        forall k: int :: 0 <= k < n ==> a.spec_index(k) <= new_max,
        0 <= new_max
    ensures
        spec_sum(a, n) + new_max <= (n + 1) * new_max
{
    spec_sum_bound(a, n, new_max);
    assert(spec_sum(a, n) <= n * new_max);
    assert(spec_sum(a, n) + new_max <= n * new_max + new_max);
    assert(spec_sum(a, n) + new_max <= (n + 1) * new_max);
}

}