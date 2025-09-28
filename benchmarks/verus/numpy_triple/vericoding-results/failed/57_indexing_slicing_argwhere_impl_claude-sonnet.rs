// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn argwhere(a: &Vec<f64>) -> (indices: Vec<usize>)
    ensures
        forall|i: int| 0 <= i < indices@.len() ==> (#[trigger] indices@[i] as int) < a@.len(),
        forall|i: int| 0 <= i < indices@.len() ==> a@[indices@[i] as int] != 0.0,
        forall|i: int| 0 <= i < a@.len() && a@[i] != 0.0 ==> exists|j: int| 0 <= j < indices@.len() && indices@[j] as int == i,
        forall|i: int, j: int| 0 <= i < indices@.len() && 0 <= j < indices@.len() && i != j ==> indices@[i] != indices@[j],
        forall|i: int, j: int| 0 <= i < indices@.len() && 0 <= j < indices@.len() && (indices@[i] as int) < (indices@[j] as int) ==> i < j,
        (indices@.len() == 0) == (forall|i: int| 0 <= i < a@.len() ==> a@[i] == 0.0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed assert syntax by removing line break in forall assertion */
    let mut indices = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|k: int| 0 <= k < indices@.len() ==> (#[trigger] indices@[k] as int) < a@.len(),
            forall|k: int| 0 <= k < indices@.len() ==> a@[indices@[k] as int] != 0.0,
            forall|k: int| 0 <= k < i && a@[k] != 0.0 ==> exists|j: int| 0 <= j < indices@.len() && indices@[j] as int == k,
            forall|k: int, j: int| 0 <= k < indices@.len() && 0 <= j < indices@.len() && k != j ==> indices@[k] != indices@[j],
            forall|k: int, j: int| 0 <= k < indices@.len() && 0 <= j < indices@.len() && (indices@[k] as int) < (indices@[j] as int) ==> k < j,
        decreases a.len() - i
    {
        if a[i] != 0.0 {
            proof {
                assert(i < a.len());
                assert(a@[i as int] != 0.0);
                let old_len = indices@.len();
                assert(forall|k: int| 0 <= k < old_len ==> indices@[k] as int < i);
            }
            indices.push(i);
            proof {
                assert(indices@[indices@.len() - 1] as int == i as int);
                assert(forall|k: int| 0 <= k < indices@.len() - 1 ==> indices@[k] as int < i);
                assert(forall|k: int| 0 <= k < indices@.len() - 1 ==> indices@[k] != indices@[indices@.len() - 1]);
            }
        }
        i += 1;
    }
    proof {
        assert(i == a.len());
        assert(forall|k: int| 0 <= k < a@.len() && a@[k] != 0.0 ==> exists|j: int| 0 <= j < indices@.len() && indices@[j] as int == k);
        if indices@.len() == 0 {
            assert(forall|k: int| 0 <= k < a@.len() ==> a@[k] == 0.0);
        } else {
            assert(exists|k: int| 0 <= k < a@.len() && a@[k] != 0.0);
        }
    }
    indices
}
// </vc-code>

}
fn main() {}