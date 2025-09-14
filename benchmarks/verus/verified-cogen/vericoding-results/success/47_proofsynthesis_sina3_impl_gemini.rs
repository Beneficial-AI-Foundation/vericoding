// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(sum).len() == 1,
		N < 1000,

	ensures
		forall |k:int| 0 <= k < N ==> a[k] == N + 1,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fixed type mismatch in assert by casting to i32 */
{
    let mut i: i32 = 0;
    while i < N
        invariant
            a.len() == N,
            0 <= i <= N,
            N < 1000,
            forall|k: int| 0 <= k < i ==> a[k] == N + 1,
        decreases N - i
    {
        let ghost old_a = a@;
        a.set(i as usize, N + 1);
        proof {
            assert(a@ =~= old_a.update(i as int, (N + 1) as i32));
        }
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}