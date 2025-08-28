use vstd::prelude::*;

verus!{

// <vc-helpers>
spec fn in_bounds<T>(v: &Vec<T>, i: int) -> bool {
    0 <= i < v.len()
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
    // impl-start
    let mut sum = 0i32;
    let mut i = 0;
    
    while i < N
        invariant 
            0 <= i <= N,
            i <= sum <= 2 * i,
            forall |k:int| 0 <= k < b.len() ==> k <= #[trigger] b[k] <= k + 1,
        decreases N - i
    {
        sum = sum + b[i as usize];
        i = i + 1;
    }
    
    sum
    // impl-end
}
// </vc-code>

}

fn main() {}