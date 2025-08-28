use vstd::prelude::*;

verus!{

// <vc-helpers>
// No updates needed in helpers for this fix
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
    let mut sum: i32 = 0;
    let mut i: i32 = 0;
    while i < N
        invariant
            0 <= i <= N,
            i <= sum <= 2 * i,
            forall |k: int| 0 <= k < i ==> k <= b@[k] <= k + 1,
        decreases N - i
    {
        a.push(b@[i]);
        sum = sum + b@[i];
        i = i + 1;
    }
    sum
}
// </vc-code>

}

fn main() {}