// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): unchanged from previous iteration */
proof fn lemma_search_property(a: Seq<i32>, i: int, j: int)
    requires
        0 <= i <= j < a.len(),
        forall|k: int| 0 < k < a.len() ==> #[trigger] a[k] >= a[k-1] - 1,
    ensures
        a[j] >= a[i] - (j - i),
    decreases j - i,
{
    if i < j {
        lemma_search_property(a, i, j - 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn find_zero(a: &[i32]) -> (index: i32)
    requires
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] >= 0,
        forall|i: int| 0 < i < a.len() ==> #[trigger] a[i-1] - 1 <= a[i],
    ensures
        (index < 0 ==> forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] != 0),
        (0 <= index ==> index < a.len() && a[index as int] == 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed compilation error by introducing let-bindings for casts in proof block */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i as int ==> a@[j] != 0,
        decreases a.len() - i,
    {
        let v = a[i];
        if v == 0 {
            return i as i32;
        }

        let next_i = i + (v as usize);
        proof {
            let i_int = i as int;
            let next_i_int = next_i as int;
            let len_int = a.len() as int;
            assert forall|j: int| i_int < j && j < next_i_int && j < len_int implies a@[j] > 0 by {
                lemma_search_property(a@, i_int, j);
            }
        }
        
        i = next_i;
    }

    return -1;
}
// </vc-code>

}
fn main() {}