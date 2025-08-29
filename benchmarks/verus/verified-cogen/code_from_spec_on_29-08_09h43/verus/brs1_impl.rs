use vstd::prelude::*;

verus!{

// <vc-helpers>

// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    // pre-conditions-start
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        sum[0] <= N,
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    let mut count = 0i32;
    let mut i = 0;
    /* code modified by LLM (iteration 3): explicit type annotation for count and bounds check */
    while i < a.len()
        invariant
            i <= a.len(),
            count <= i,
            count <= N,
            0 <= count < N + 1,
        decreases a.len() - i
    {
        if a[i] > 0 {
            /* code modified by LLM (iteration 3): added bounds check before increment */
            if count < N {
                count += 1;
            }
        }
        i += 1;
    }
    sum.set(0, count);
    // impl-end
}
// </vc-code>

}

fn main() {}