use vstd::prelude::*;

verus!{

// <vc-helpers>
proof fn sum_bounds_lemma(b: &Vec<i32>, start: int, end: int)
    requires 
        0 <= start <= end <= b.len(),
        forall |k:int| 0 <= k < b.len() ==> start <= k < end ==> k <= #[trigger] b[k] <= k + 1,
    ensures
        start <= end * (end - 1) / 2 + (end - start) <= 2 * end,
{
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
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == N,
            b.len() == N,
            forall |k:int| 0 <= k < b.len() ==> k <= #[trigger] b[k] <= k + 1,
            i as i32 <= sum <= 2 * (i as i32),
            sum <= 0x3FFF_FFFF,
        decreases a.len() - i,
    {
        sum = sum + b[i];
        i = i + 1;
    }
    
    sum
}
// </vc-code>

}

fn main() {}