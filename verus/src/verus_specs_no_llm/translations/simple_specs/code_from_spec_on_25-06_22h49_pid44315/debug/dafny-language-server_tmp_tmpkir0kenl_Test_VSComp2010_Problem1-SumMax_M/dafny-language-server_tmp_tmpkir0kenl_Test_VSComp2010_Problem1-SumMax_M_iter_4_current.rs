use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn M(N: int, a: Vec<int>) -> (sum: int, max: int)
    requires
        0 <= N && a.len() == N && (forall k :: 0 <= k && k < N ==> 0 <= a.spec_index(k))
    ensures
        sum <= N * max
{
    if N == 0 {
        return (0, 0);
    }
    
    let mut sum: int = 0;
    let mut max: int = a[0];
    let mut i: int = 0;
    
    while i < N
        invariant
            0 <= i <= N,
            0 <= sum,
            0 <= max,
            sum <= i * max,
            forall k :: 0 <= k < i ==> a.spec_index(k) <= max,
            sum == spec_sum(a, i),
            i == 0 || (exists k :: 0 <= k < i && a.spec_index(k) == max)
        decreases N - i
    {
        proof {
            assert(0 <= i < N);
            assert(i < a.len());
        }
        let current = a[i as usize];
        
        // Update sum and max with proper proof obligations
        sum = sum + current;
        if current > max {
            // Prove the new max maintains the invariant
            proof {
                assert(forall k :: 0 <= k < i ==> a.spec_index(k) <= max);
                assert(current > max);
                assert(forall k :: 0 <= k < i ==> a.spec_index(k) < current);
            }
            max = current;
            proof {
                // After updating max, we need to re-establish sum <= (i+1) * max
                assert(sum == spec_sum(a, i) + current);
                assert(max == current);
                spec_sum_bound_with_new_max(a, i, current);
            }
        } else {
            proof {
                // max doesn't change, so we need to prove sum <= (i+1) * max
                assert(sum == spec_sum(a, i) + current);
                assert(current <= max);
                assert(spec_sum(a, i) <= i * max);
                assert(sum <= i * max + max);
                assert(sum <= (i + 1) * max);
            }
        }
        
        i = i + 1;
    }
    
    // Final proof that sum <= N * max
    proof {
        assert(i == N);
        assert(sum == spec_sum(a, N));
        assert(forall k :: 0 <= k < N ==> a.spec_index(k) <= max);
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
        forall k :: 0 <= k < n ==> a.spec_index(k) <= bound
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
        forall k :: 0 <= k < n ==> a.spec_index(k) < new_max
    ensures
        spec_sum(a, n) + new_max <= (n + 1) * new_max
    decreases n
{
    if n <= 0 {
        assert(spec_sum(a, 0) + new_max == 0 + new_max);
        assert(0 + new_max <= 1 * new_max);
    } else {
        assert(forall k :: 0 <= k < n ==> a.spec_index(k) < new_max);
        assert(forall k :: 0 <= k < n ==> a.spec_index(k) <= new_max - 1);
        spec_sum_bound(a, n, new_max - 1);
        assert(spec_sum(a, n) <= n * (new_max - 1));
        assert(spec_sum(a, n) + new_max <= n * (new_max - 1) + new_max);
        assert(spec_sum(a, n) + new_max <= n * new_max - n + new_max);
        assert(spec_sum(a, n) + new_max <= (n + 1) * new_max - n);
        assert(spec_sum(a, n) + new_max <= (n + 1) * new_max);
    }
}

}