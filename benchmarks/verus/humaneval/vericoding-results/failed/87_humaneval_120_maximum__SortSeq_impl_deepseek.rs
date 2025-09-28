// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Use index mutation with vector instead of swap method */
fn swap_lemma(v: Vec<i8>, i: usize, j: usize) -> (swapped: Vec<i8>)
    requires
        i < v@.len(),
        j < v@.len(),
    ensures
        swapped@.len() == v@.len(),
        swapped@.to_multiset() == v@.to_multiset(),
{
    let mut result = v.clone();
    let temp = result[i];
    result[i] = result[j];
    result[j] = temp;
    result
}

fn insertion_sort_helper(v: &mut Vec<i8>, i: usize)
    requires
        i <= v@.len(),
    ensures
        v@.len() == old(v)@.len(),
        v@.to_multiset() == old(v)@.to_multiset(),
        forall|k: int, l: int| 0 <= k < l < i ==> v@[k] <= v@[l],
{
    if i == 0 {
        return;
    }
    let mut j: usize = i - 1;
    while j > 0
        invariant
            0 <= j <= i <= v@.len(),
            v@.len() == old(v)@.len(),
            v@.to_multiset() == old(v)@.to_multiset(),
        decreases j
    {
        if v[j - 1] > v[j] {
            let temp = v[j - 1];
            v[j - 1] = v[j];
            v[j] = temp;
        }
        j = j - 1;
    }
    if i > 1 {
        insertion_sort_helper(v, i - 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn sort_seq(s: &Vec<i8>) -> (sorted: Vec<i8>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < sorted@.len() ==> #[trigger] sorted@[i] <= #[trigger] sorted@[j],
        sorted@.len() == s@.len(),
        s@.to_multiset() == sorted@.to_multiset(),
        forall|i: int| 0 <= i < s@.len() ==> exists|j: int| 0 <= j < sorted@.len() && #[trigger] s@[i] == #[trigger] sorted@[j],
        forall|x: i8| #[trigger] s@.contains(x) ==> #[trigger] sorted@.contains(x),
        forall|i: int| 0 <= i < s@.len() ==> exists|j: int| 0 <= j < sorted@.len() && #[trigger] sorted@[i] == #[trigger] s@[j],
        forall|x: i8| #[trigger] sorted@.contains(x) ==> #[trigger] s@.contains(x),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Use same implementation but with manual swap fix */
{
    let mut sorted = s.clone();
    let len: usize = sorted.len();
    insertion_sort_helper(&mut sorted, len);
    sorted
}
// </vc-code>


}

fn main() {}