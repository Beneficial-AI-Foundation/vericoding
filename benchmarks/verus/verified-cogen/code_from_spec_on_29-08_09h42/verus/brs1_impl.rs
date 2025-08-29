use vstd::prelude::*;

verus!{

// <vc-helpers>
proof fn sum_bound_lemma(a: &Vec<i32>, N: i32)
    requires
        N > 0,
        a.len() == N,
    ensures
        a@.fold_left(0int, |acc: int, x: i32| acc + x as int) <= N || a@.fold_left(0int, |acc: int, x: i32| acc + x as int) >= N,
{
}
// </vc-helpers>

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
    /* code modified by LLM (iteration 3): added decreases clause to fix verification error */
    let mut total: i32 = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == N,
            N > 0,
            sum.len() == 1,
            total <= N,
        decreases a.len() - i,
    {
        if total <= N - 1 {
            total = total + 1;
        }
        i = i + 1;
    }
    
    sum[0] = total;
    // impl-end
}
// </vc-code>

}

fn main() {}