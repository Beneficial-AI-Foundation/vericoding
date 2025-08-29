use vstd::prelude::*;

verus!{

// <vc-helpers>
spec fn lemma_total_bound(a: &Vec<i32>, i: usize, total: i32)
    requires
        i <= a.len(),
        forall|j: int| 0 <= j < i ==> a@[j] <= 4 || a@[j] > 4,
        total == (0..i as int).fold(0, |acc, j| acc + if a@[j] <= 4 { a@[j] } else { 4 }),
    ensures
        total <= 4 * (i as i32),
{
    if i == 0 {
        assert(total == 0);
    } else {
        let prev_i = i - 1;
        let prev_total = (0..prev_i as int).fold(0, |acc, j| acc + if a@[j] <= 4 { a@[j] } else { 4 });
        lemma_total_bound(a, prev_i, prev_total);
        assert(prev_total <= 4 * (prev_i as i32));
        
        let added = if a@[prev_i as int] <= 4 { a@[prev_i as int] } else { 4 };
        assert(added <= 4);
        assert(total == prev_total + added);
        assert(total <= 4 * (prev_i as i32) + 4);
        assert(total <= 4 * (i as i32));
    }
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 
	// pre-conditions-start
	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
		N < 1000,
	// pre-conditions-end
	// post-conditions-start
	ensures
		sum[0] <= 4 * N,
	// post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    let mut total: i32 = 0;
    let mut i: usize = 0;
    /* code modified by LLM (iteration 5): added overflow bounds and proof block */
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == N,
            sum.len() == 1,
            N > 0,
            N < 1000,
            total <= 4 * (i as i32),
            total >= 0,
            total < 4000,
        decreases a.len() - i
    {
        if a[i] <= 4 {
            /* code modified by LLM (iteration 5): added proof for overflow prevention */
            proof {
                assert(total < 4000);
                assert(a[i] <= 4);
                assert(total + a[i] <= total + 4 < 4000 + 4);
                assert(4 * ((i + 1) as i32) <= 4 * (N as i32));
                assert(4 * (N as i32) < 4000);
            }
            total = total + a[i];
        } else {
            /* code modified by LLM (iteration 5): added proof for overflow prevention */
            proof {
                assert(total < 4000);
                assert(total + 4 < 4000 + 4);
                assert(4 * ((i + 1) as i32) <= 4 * (N as i32));
                assert(4 * (N as i32) < 4000);
            }
            total = total + 4;
        }
        i = i + 1;
    }
    sum.set(0, total);
    // impl-end
}
// </vc-code>

}

fn main() {}