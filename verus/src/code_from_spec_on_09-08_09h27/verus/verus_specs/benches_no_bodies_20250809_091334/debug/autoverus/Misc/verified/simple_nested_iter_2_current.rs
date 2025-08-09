use vstd::prelude::*;
fn main() {}
verus!{
pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires 
        forall |k:int| 0 <= k < b.len() ==> k <= #[trigger] b@[k] <= k + 1,
        old(a).len() == N,
        b.len() == N,
        N >= 0,
        N <= 0x3FFF_FFFF,
    ensures
        N <= sum <= 2*N
{  
    let mut sum = 0;
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause and fixed invariant bounds */
    while i < N
        invariant
            0 <= i <= N,
            i <= sum <= 2 * i,
        decreases N - i
    {
        /* code modified by LLM (iteration 1): added proof block to establish bounds */
        proof {
            assert(0 <= i < b.len());
            assert(i <= b@[i as int] <= i + 1);
        }
        sum = sum + b[i as usize];
        i = i + 1;
    }
    
    sum
}
}