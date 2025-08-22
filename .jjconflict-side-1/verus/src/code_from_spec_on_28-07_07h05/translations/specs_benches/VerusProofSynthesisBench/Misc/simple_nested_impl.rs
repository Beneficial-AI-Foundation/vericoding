use vstd::prelude::*;

verus!{

/* code modified by LLM (iteration 2): Moved spec function outside of executable function */
spec fn sum_up_to(b: Seq<i32>, end: int) -> int
    decreases end
{
    if end <= 0 { 0 } else { sum_up_to(b, end - 1) + b[end - 1] }
}

fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    // pre-conditions-start
    requires 
        forall |k:int| 0 <= k < b.len() ==> k <= #[trigger] b[k] <= k + 1,
        old(a).len() == N,
        b.len() == N,
        N <= 0x3FFF_FFFF,
        N >= 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        N <= sum <= 2*N,
    // post-conditions-end
{  
    let mut result: i32 = 0;
    let mut i: usize = 0;
    
    /* code modified by LLM (iteration 3): Added decreases clause to prove loop termination */
    while i < b.len()
        invariant
            i <= b.len(),
            /* code modified by LLM (iteration 2): Fixed spec function usage */
            result == sum_up_to(b@, i as int),
            /* code modified by LLM (iteration 2): Added bounds invariant based on the constraint that k <= b[k] <= k + 1 */
            (i as int) <= result <= 2 * (i as int),
        decreases b.len() - i
    {
        result = result + b[i];
        i = i + 1;
    }
    
    result
}
}

fn main() {}