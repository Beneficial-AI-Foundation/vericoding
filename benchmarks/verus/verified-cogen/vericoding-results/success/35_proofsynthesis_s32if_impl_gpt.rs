// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
spec fn four(n: nat) -> nat { 4 * n }

proof fn four_additive(n: nat, m: nat)
    ensures
        four(n + m) == four(n) + four(m)
{
}

// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)

	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,

	ensures
		sum[0] == 4 * N,
// </vc-spec>
// <vc-code>
{
    let init_len = sum.len();
    while sum.len() > 0
        invariant
            sum.len() <= init_len,
        decreases sum.len()
    {
        let _ = sum.pop();
    }
    sum.push(0);
    let val: i32 = 4 * (N as i32);
    sum[0] = val;
}

// </vc-code>

}
fn main() {}