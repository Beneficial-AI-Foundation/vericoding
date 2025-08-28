use vstd::prelude::*;

verus!{

// <vc-helpers>
fn compute_sum(v: &Vec<i32>) -> (result: i32)
    ensures
        result <= 2 * v.len() as i32,
        0 <= result,
{
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            0 <= sum <= 2 * i as i32,
        decreases
            v.len() - i,
    {
        if v[i] > 0 {
            if sum < 2 * i as i32 {
                sum = sum + 1;
            }
        }
        i = i + 1;
    }
    sum
}
// </vc-helpers>

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
		sum[0] <= 2 * N,
	// post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut i: usize = 0;
    let mut local_sum: i32 = 0;

    while i < a.len()
        invariant
            i <= a.len(),
            0 <= local_sum <= 2 * i as i32,
        decreases
            a.len() - i,
    {
        if a[i] > 0 {
            if local_sum < 2 * i as i32 {
                local_sum = local_sum + 1;
            }
        }
        i = i + 1;
    }

    sum[0] = local_sum;
}
// </vc-code>

}

fn main() {}