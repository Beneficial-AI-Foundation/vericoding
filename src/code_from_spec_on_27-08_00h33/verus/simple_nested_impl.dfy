use vstd::prelude::*;

verus!{

// <vc-helpers>
spec fn sum_bounds(b: Seq<i32>, N: int) -> bool {
    forall |k: int| 0 <= k < N ==> k <= b[k] <= k + 1
}

proof fn lemma_sum_bounds(b: &Vec<i32>, N: i32)
    requires
        forall |k:int| 0 <= k < N ==> k <= #[trigger] b@[k] <= k + 1,
        b.len() == N,
        N >= 0,
    ensures
        N <= (0..N as usize).fold(0, |acc: int, i: usize| acc + b@[i as int] as int) <= 2*N,
{
    if N == 0 {
        return;
    }
    
    let mut sum_min = 0;
    let mut sum_max = 0;
    let mut i = 0;
    
    while i < N
        invariant
            0 <= i <= N,
            sum_min == i,
            sum_max == 2 * i,
            forall |k:int| 0 <= k < N ==> k <= b@[k] <= k + 1,
    {
        sum_min += i;
        sum_max += i + 1;
        i += 1;
    }
    
    assert(sum_min == N * (N - 1) / 2);
    assert(sum_max == N * (N + 1) / 2);
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
    if N <= 0 {
        return 0;
    }
    
    let mut sum = 0;
    let mut i = 0;
    
    while i < N
        invariant
            0 <= i <= N,
            i <= sum <= 2 * i,
            forall |k:int| 0 <= k < N ==> k <= b@[k] <= k + 1,
            b.len() == N,
    {
        sum += b[i as usize];
        i += 1;
    }
    
    proof {
        assert(forall |k:int| 0 <= k < N ==> k <= b@[k] <= k + 1);
    }
    
    sum
}
// </vc-code>

}

fn main() {}