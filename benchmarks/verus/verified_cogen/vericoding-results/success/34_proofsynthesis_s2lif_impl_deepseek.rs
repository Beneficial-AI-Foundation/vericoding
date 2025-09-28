// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): ensure proper nat conversion with explicit casting */
spec fn compute_triple(n: nat) -> nat { 3 * n }
proof fn triple_lemma(n_nat: nat) 
    ensures compute_triple(n_nat) == 3 * n_nat 
{
    assert(compute_triple(n_nat) == 3 * n_nat) by (nonlinear_arith);
}
// </vc-helpers>

// <vc-spec>
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,

	ensures
		sum[0] == 3 * N,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): use lemma to prove equality before assignment */
{
    proof {
        let n_nat = N as nat;
        triple_lemma(n_nat);
    }
    
    let triple_val: i32 = (3 * N) as i32;
    sum[0] = triple_val;
}
// </vc-code>

}
fn main() {}