use vstd::prelude::*;
fn main() {}
verus!{
pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires 
        forall |k:int| k <= #[trigger] b[k] <= k + 1,
        old(a).len() == N,
        b.len() == N,
        N <= 0x3FFF_FFFF,
    ensures
        N <= sum <= 2*N
{  
    let mut sum = 0;
    let mut i = 0;
    
    while i < N
        invariant
            0 <= i <= N,
            i <= sum <= 2 * i,
    {
        sum = sum + b[i as usize];
        i = i + 1;
    }
    
    sum
}
}