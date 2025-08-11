use vstd::prelude::*;
fn main() {}
verus!{

pub fn myfun(a: &mut Vec<u32>, N: u32) -> (sum: u32)
    requires 
        old(a).len() == N,
        N <= 0x7FFF_FFFF,
    ensures
        sum <= 2 * N,
{
    let mut result: u32 = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            result <= 2 * i,
        /* code modified by LLM (iteration 1): added decreases clause for loop termination */
        decreases a.len() - i
    {
        if result < 2 * N - 2 {
            if result + 2 <= 2 * N {
                result = result + 2;
            }
        }
        i = i + 1;
    }
    
    result
}
}