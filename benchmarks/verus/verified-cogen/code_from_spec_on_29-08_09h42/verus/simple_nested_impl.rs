use vstd::prelude::*;

verus!{

// <vc-helpers>
lemma_by_forall! {
    lemma forall_b_bounds(b: &Vec<i32>, N: i32, k: int)
        requires 
            forall |j:int| 0 <= j < N ==> j <= #[trigger] b@[j] <= j + 1,
            b.len() == N,
            0 <= k < N
        ensures k <= b@[k] <= k + 1
    {
        assert(k <= b@[k] <= k + 1);
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
    
    /* code modified by LLM (iteration 5): fixed precondition bounds and added proof for array access */
    while i < N
        invariant
            0 <= i <= N,
            i <= sum <= 2 * i,
        decreases N - i
    {
        proof {
            assert(0 <= i < N);
            assert(i < b.len() as i32);
            assert(0 <= i < b.len());
            forall_b_bounds(b, N, i as int);
            assert(i <= b@[i as int] <= i + 1);
            assert((sum as int) + b@[i as int] <= (sum as int) + (i + 1));
            assert((sum as int) + b@[i as int] <= 2 * i + (i + 1));
            assert((sum as int) + b@[i as int] <= 2 * (i + 1));
        }
        sum += b[i as usize];
        i += 1;
    }
    
    sum
}
// </vc-code>

}

fn main() {}