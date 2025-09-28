use vstd::prelude::*;

verus! {

// VSComp 2010, problem 1, compute the sum and max of the elements of an array and prove
// that 'sum <= N * max'.
// Rustan Leino, 18 August 2010.
//
// The problem statement gave the pseudo-code for the method, but did not ask to prove
// that 'sum' or 'max' return as the sum and max, respectively, of the array.  The
// given assumption that the array's elements are non-negative is not needed to establish
// the requested postcondition.

// <vc-helpers>
spec fn sum_of_range(a: &[int], start: int, end: int) -> int
    decreases end - start
{
    if start >= end {
        0
    } else {
        a[start] + sum_of_range(a, start + 1, end)
    }
}

spec fn max_of_range(a: &[int], start: int, end: int) -> int
    requires start < end, end <= a.len()
    decreases end - start
{
    if start + 1 == end {
        a[start]
    } else {
        let rest_max = max_of_range(a, start + 1, end);
        if a[start] >= rest_max { a[start] } else { rest_max }
    }
}

proof fn sum_max_property(a: &[int], n: int)
    requires 
        0 < n <= a.len(),
        forall|k: int| 0 <= k < n ==> 0 <= a[k]
    ensures 
        sum_of_range(a, 0, n) <= n * max_of_range(a, 0, n)
    decreases n
{
    if n == 1 {
        assert(sum_of_range(a, 0, 1) == a[0]);
        assert(max_of_range(a, 0, 1) == a[0]);
    } else {
        sum_max_property(a, n - 1);
        let prev_sum = sum_of_range(a, 0, n - 1);
        let prev_max = max_of_range(a, 0, n - 1);
        let curr_max = max_of_range(a, 0, n);
        
        assert(prev_sum <= (n - 1) * prev_max);
        assert(curr_max >= prev_max);
        assert(curr_max >= a[n - 1]);
        assert(sum_of_range(a, 0, n) == prev_sum + a[n - 1]);
        assert(prev_sum + a[n - 1] <= (n - 1) * curr_max + curr_max);
        assert((n - 1) * curr_max + curr_max == n * curr_max);
    }
}
// </vc-helpers>

// <vc-spec>
fn M(N: int, a: &[int]) -> (result: (int, int))
    requires 
        0 <= N,
        a.len() == N,
        forall|k: int| 0 <= k && k < N ==> 0 <= a[k],
    ensures 
        result.0 <= N * result.1;
// </vc-spec>
// <vc-code>
{
    if N == 0 {
        return (0, 0);
    }
    
    let mut sum = a[0];
    let mut max = a[0];
    let mut i = 1;
    
    while i < N
        invariant
            1 <= i <= N,
            sum == sum_of_range(a, 0, i),
            max == max_of_range(a, 0, i),
            sum <= i * max,
    {
        sum = sum + a[i];
        if a[i] > max {
            max = a[i];
        }
        i = i + 1;
        
        proof {
            sum_max_property(a, i);
        }
    }
    
    (sum, max)
}
// </vc-code>

fn main() {}

}