// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn last_position(a: &[i32], elem: i32) -> (result: usize)
    requires
        0 < a.len() < 100_000,
        exists|i: int| 0 <= i < a.len() && a[i] == elem,
    ensures
        0 <= result < a.len(),
        forall|i: int| result < i < a.len() ==> a[i] != elem,
        a[result as int] == elem,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added decreases clause to the loop */
    let mut i: usize = 0;
    let mut result_opt: Option<usize> = None;

    while i < a.len()
        invariant
            0 <= i <= a.len(),
            match result_opt {
                Some(result_idx) => {
                    &&& 0 <= result_idx < i
                    &&& a[result_idx as int] == elem
                    &&& forall|k: int| result_idx < k < i ==> a[k] != elem
                },
                None => {
                    &&& forall|k: int| 0 <= k < i ==> a[k] != elem
                }
            },
        decreases a.len() - i,
    {
        if a[i] == elem {
            result_opt = Some(i);
        }
        i = i + 1;
    }

    proof {
        let witness_idx = choose |k: int| 0 <= k < a.len() && a[k] == elem;
        match result_opt {
            Some(result_idx) => { }
            None => {
                assert(forall|k: int| 0 <= k < a.len() ==> a[k] != elem); // loop invariant implies this
                assert(a[witness_idx] != elem); // contradiction with requires
                assert(false);
            }
        }
        assert(result_opt is Some);
    }

    let result = result_opt.unwrap();
    result
}
// </vc-code>

}
fn main() {}