// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed bounds checking and overflow issues */
fn insertion_sort_even_positions(a: Vec<i8>) -> (result: Vec<i8>)
    requires
        a@.len() > 0
    ensures
        result@.len() == a@.len(),
        forall|i: int| 0 <= i < a@.len() && i % 2 == 1 ==> #[trigger] result@[i] == #[trigger] a@[i],
        a@.to_multiset() == result@.to_multiset(),
        forall|i: int, j: int| 0 <= i < j && 2 * i < result@.len() && 2 * j < result@.len() ==> #[trigger] result@[2 * i] <= #[trigger] result@[2 * j]
{
    let mut sorted = a.clone();
    let mut pos: usize = 2;
    while pos < sorted.len()
        invariant
            sorted@.len() == a@.len(),
            forall|i: int| 0 <= i < a@.len() && i % 2 == 1 ==> #[trigger] sorted@[i] == #[trigger] a@[i],
            a@.to_multiset() == sorted@.to_multiset(),
            forall|i: int, j: int| 0 <= i < j && 2 * i < pos && 2 * j < pos ==> #[trigger] sorted@[2 * i] <= #[trigger] sorted@[2 * j],
            pos % 2 == 0,
            2 <= pos <= sorted@.len()
        decreases sorted@.len() - pos
    {
        let key = sorted[pos];
        let mut j: usize = pos;
        while j >= 2 && j - 2 < sorted.len() && sorted[j - 2] > key
            invariant
                sorted@.len() == a@.len(),
                forall|i: int| 0 <= i < a@.len() && i % 2 == 1 ==> #[trigger] sorted@[i] == #[trigger] a@[i],
                j % 2 == 0,
                2 <= j <= pos,
                j < sorted@.len(),
                forall|i: int, k: int| 0 <= i < k && 2 * i < pos && 2 * k < pos && 2 * i < sorted@.len() && 2 * k < sorted@.len() && (2 * i < j || 2 * k < j) ==> #[trigger] sorted@[2 * i] <= #[trigger] sorted@[2 * k]
            decreases j
        {
            sorted.set(j, sorted[j - 2]);
            j = j - 2;
        }
        sorted.set(j, key);
        if pos + 2 < usize::MAX {
            pos = pos + 2;
        } else {
            break;
        }
    }
    sorted
}
// </vc-helpers>

// <vc-spec>
fn sorted_even(a: Vec<i8>) -> (sorted: Vec<i8>)
    requires 
        a@.len() > 0
    ensures 
        sorted@.len() == a@.len(),
        forall|i: int, j: int| 0 <= i < j && 2 * i < sorted@.len() && 2 * j < sorted@.len() ==> #[trigger] sorted@[2 * i] <= #[trigger] sorted@[2 * j],
        forall|i: int| 0 <= i < a@.len() && i % 2 == 1 ==> #[trigger] sorted@[i] == #[trigger] a@[i],
        a@.to_multiset() == sorted@.to_multiset()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): calling helper function */
    insertion_sort_even_positions(a)
}
// </vc-code>


}

fn main() {}