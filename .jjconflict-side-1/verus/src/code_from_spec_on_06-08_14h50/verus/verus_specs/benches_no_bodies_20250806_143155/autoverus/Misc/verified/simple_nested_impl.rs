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
    let mut total: i32 = 0;
    let mut i: usize = 0;
    
    while i < b.len()
        invariant
            0 <= i <= b.len(),
            i as int <= total <= 2 * (i as int),
        decreases b.len() - i
    {
        total += b[i];
        i += 1;
    }
    
    total
}
}