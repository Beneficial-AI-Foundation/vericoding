use vstd::prelude::*;
fn main() {}
verus!{
//IMPL simple_nested
pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires 
        forall |k:int| 0 <= k < b.len() ==> k <= #[trigger] b[k] <= k + 1,
        old(a).len() == N,
        b.len() == N,
        N <= 0x3FFF_FFFF,
    ensures
        N <= sum <= 2*N
{
    let mut result: i32 = 0;
    let mut i: usize = 0;
    
    /* code modified by LLM (iteration 3): fixed loop invariant and assertions to properly handle bounds and overflow */
    while i < b.len()
        invariant
            i <= b.len(),
            0 <= i <= N,
            (i as int) <= result <= 2 * (i as int),
            b.len() == N,
            forall |k:int| 0 <= k < b.len() ==> k <= #[trigger] b[k] <= k + 1,
        decreases b.len() - i
    {
        /* code modified by LLM (iteration 3): proper bounds checking and simplified assertions */
        assert(i < b.len());
        assert(0 <= i < b.len());
        assert((i as int) <= b[i as int] <= (i as int) + 1);
        
        /* code modified by LLM (iteration 3): establish result bounds after addition */
        let old_result = result;
        result = result + b[i];
        
        assert(old_result + (i as int) <= result <= old_result + (i as int) + 1);
        assert(result <= 2 * (i as int) + (i as int) + 1);
        assert(result <= 2 * ((i as int) + 1));
        
        i = i + 1;
    }
    
    /* code modified by LLM (iteration 3): final assertion to establish postcondition */
    assert(i == b.len());
    assert(b.len() == N);
    assert((N as int) <= result <= 2 * (N as int));
    
    result
}
}