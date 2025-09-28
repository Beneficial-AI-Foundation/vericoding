// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn M(N: i32, a: &[i32]) -> (result: (i32, i32))
    requires 
        0 <= N,
        a.len() == N,
        (forall|k: int| 0 <= k && k < N ==> 0 <= a[k]),
    ensures 
        result.0 <= N * result.1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [Fixed compilation error and added assertion for invariant proof.] */
    let mut i: i32 = 0;
    let mut sum: i32 = 0;
    let mut max: i32 = 0;

    while i < N
        invariant
            0 <= i <= N,
            (forall|k: int| 0 <= k < i ==> a@[k] <= max),
            0 <= max,
            sum as int <= i as int * max as int,
        decreases N - i
    {
        let current_val = a[i as usize];
        
        if current_val > max {
            proof {
                vstd::arithmetic::lemmas::mul_le_mono_nonneg_left(i as int, max as int, current_val as int);
            }
            max = current_val;
        }

        assert(sum as int + current_val as int <= i as int * max as int + max as int);
        
        sum = sum + current_val;
        i = i + 1;
    }
    
    (sum, max)
}
// </vc-code>

}
fn main() {}