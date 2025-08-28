use vstd::prelude::*;

verus!{

// <vc-helpers>
spec fn nat_to_int(n: nat) -> int {
    n as int
}

spec fn nat_to_i32(n: nat) -> i32 {
    n as i32
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
		sum[0] <= 3 * N,
	// post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    let mut total = 0i32;
    let mut i = 0;
    
    while i < N
        invariant
            0 <= i <= N,
            i <= nat_to_int(a@.len()),
            total <= 3 * i,
        decreases N - i
    {
        if i < nat_to_i32(a@.len()) {
            if a[i as usize] <= 3 {
                total = total + a[i as usize];
            } else {
                total = total + 3;
            }
        }
        i = i + 1;
    }
    
    sum.set(0, total);
    // impl-end
}
// </vc-code>

}
fn main() {}