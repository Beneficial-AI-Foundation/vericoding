// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): checks equality of first n elements */
spec fn eq_prefix(a1: &Vec<f32>, a2: &Vec<f32>, n: usize) -> bool
{
    forall|i: int| 0 <= i < n as int ==> a1@[i] == a2@[i]
}

// </vc-helpers>

// <vc-spec>
fn array_equiv(a1: Vec<f32>, a2: Vec<f32>) -> (result: bool)
    requires a1.len() == a2.len(),
    ensures result == (forall|i: int| 0 <= i < a1@.len() ==> a1@[i] == a2@[i])
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): iterative check using sequence indexing with explicit bound proofs */
    let n = a1.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            (forall|j: int| 0 <= j < i as int ==> a1@[j] == a2@[j]),
        decreases n - i
    {
        let old_i = i;
        let j: int = old_i as int;
        proof {
            assert(old_i < n);
            assert(0 <= j && j < n as int);
        }
        if a1@[j] != a2@[j] {
            proof {
                assert(0 <= j && j < n as int);
                assert(a1@[j] != a2@[j]);
                assert(! (forall|k: int| 0 <= k < n as int ==> a1@[k] == a2@[k]));
            }
            return false;
        } else {
            i = old_i + 1;
            proof {
                assert(forall|k: int| 0 <= k < i as int ==> a1@[k] == a2@[k]);
            }
        }
    }
    proof {
        assert(i == n);
        assert(forall|k: int| 0 <= k < n as int ==> a1@[k] == a2@[k]);
    }
    true
}

// </vc-code>

}
fn main() {}