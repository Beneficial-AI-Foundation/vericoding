use vstd::prelude::*;

verus!{

// <vc-helpers>
spec fn sum_bounds(b: &Vec<i32>, N: i32) -> bool {
    forall |k: int| 0 <= k < N ==> k <= #[trigger] b@[k] <= k + 1
}

proof fn lemma_sum_bounds(b: &Vec<i32>, N: nat)
    requires 
        forall |k:int| 0 <= k < N ==> k <= #[trigger] b@[k] <= k + 1,
        b.len() == N,
    ensures
        N <= (spec_sum(b, N)) <= 2*N,
    decreases N
{
    if N == 0 {
    } else {
        lemma_sum_bounds(b, (N - 1) as nat);
        assert(N - 1 <= b@[N - 1] <= N);
    }
}

spec fn spec_sum(b: &Vec<i32>, n: nat) -> int
    decreases n
{
    if n == 0 {
        0
    } else {
        b@[(n - 1) as int] + spec_sum(b, (n - 1) as nat)
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
    let mut sum = 0i32;
    let mut i = 0;
    
    while i < N
        invariant
            0 <= i <= N,
            sum == spec_sum(b, i as nat),
            forall |k:int| 0 <= k < N ==> k <= #[trigger] b@[k] <= k + 1,
            b.len() == N,
            N >= 0,
        decreases N - i
    {
        sum = sum + b[i as usize];
        i = i + 1;
    }
    
    proof {
        lemma_sum_bounds(b, N as nat);
    }
    
    sum
}
// </vc-code>

}

fn main() {}