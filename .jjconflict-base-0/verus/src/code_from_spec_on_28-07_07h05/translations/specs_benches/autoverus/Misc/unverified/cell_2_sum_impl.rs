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
        decreases a.len() - i
    {
        /* code modified by LLM (iteration 4): restructured condition to avoid arithmetic overflow by checking if result is safe before addition */
        if N >= 1 && result <= 2 * N - 2 {
            /* code modified by LLM (iteration 4): addition now safe due to condition check above */
            result += 2;
        }
        i += 1;
    }
    
    result
}
}