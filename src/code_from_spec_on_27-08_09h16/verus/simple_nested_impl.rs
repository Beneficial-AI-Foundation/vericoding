use vstd::prelude::*;

verus!{

// <vc-helpers>
spec fn sum_bounds(b: &Vec<i32>, n: int) -> bool {
    forall |k: int| 0 <= k < n ==> k <= b[k] <= k + 1
}

spec fn sum_range(b: &Vec<i32>, n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { sum_range(b, n - 1) + b[(n - 1) as int] }
}

proof fn sum_range_lemma(b: &Vec<i32>, n: int)
    requires 
        n >= 0,
        b.len() == n,
        sum_bounds(b, n),
    ensures
        n <= sum_range(b, n) <= 2 * n
    decreases n
{
    if n == 0 {
        return;
    }
    
    // Prove lower bound: sum >= n
    assert forall |k: int| 0 <= k < n implies b[k] >= k by {
        assert(sum_bounds(b, n));
    }
    
    // Prove upper bound: sum <= 2*n  
    assert forall |k: int| 0 <= k < n implies b[k] <= k + 1 by {
        assert(sum_bounds(b, n));
    }
    
    if n > 0 {
        sum_range_lemma(b, n - 1);
        assert(sum_range(b, n) == sum_range(b, n - 1) + b[(n - 1) as int]);
        assert((n - 1) <= b[(n - 1) as int] <= (n - 1) + 1) by { assert(sum_bounds(b, n)); }
        assert((n - 1) <= sum_range(b, n - 1) <= 2 * (n - 1));
    }
}
// </vc-helpers>

// <vc-spec>
fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    // pre-conditions-start
    requires 
        forall |k:int| k <= #[trigger] b[k] <= k + 1,
        old(a).len() == N,
        b.len() == N,
        N <= 0x3FFF_FFFF,
    // pre-conditions-end
    // post-conditions-start
    ensures
        N <= sum <= 2*N,
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut sum = 0;
    let mut i = 0;
    
    while i < N
        invariant
            0 <= i <= N,
            sum == sum_range(b, i as int),
            i <= sum <= 2 * i,
    {
        sum = sum + b[i as usize];
        i = i + 1;
    }
    
    proof {
        sum_range_lemma(b, N as int);
        assert(sum_range(b, N as int) == sum);
    }
    
    sum
}
// </vc-code>

}

fn main() {}