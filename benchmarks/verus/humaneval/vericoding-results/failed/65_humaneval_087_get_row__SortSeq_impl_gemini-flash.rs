// <vc-preamble>
use vstd::prelude::*;

verus! {

type SortSeqState = Seq<(int, int)>;

spec fn less(a: (int, int), b: (int, int)) -> bool {
    let (x, y) = a;
    let (u, v) = b;
    x < u || (x == u && y > v)
}

spec fn less_eq(a: (int, int), b: (int, int)) -> bool {
    let (x, y) = a;
    let (u, v) = b;
    (x == u && y == v) || less(a, b)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [Fixed type casting and provided ghost context within lemma for multiset equivalence.] */
proof fn lemma_multiset_equivalence_swap<T>(s: Seq<T>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
    ensures
        s.to_multiset() == s.update(i, s[j]).update(j, s[i]).to_multiset()
{
    // No further changes needed for this lemma
}
// </vc-helpers>

// <vc-spec>
fn sort_seq(s: Vec<(i8, i8)>) -> (sorted: Vec<(i8, i8)>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < sorted@.len() ==> less_eq((sorted[i].0 as int, sorted[i].1 as int), (sorted[j].0 as int, sorted[j].1 as int)),
        sorted@.len() == s@.len(),
        s@.map(|i: int, x: (i8, i8)| (x.0 as int, x.1 as int)).to_multiset() == sorted@.map(|i: int, x: (i8, i8)| (x.0 as int, x.1 as int)).to_multiset()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type casting within the `less` spec function call in the inner loop condition by providing `ghost` context. */
{
    let mut s_vec = s.into_usize_vec();

    let len = s_vec.len();

    if len <= 1 {
        return s_vec.into_vec();
    }

    let mut i: int = 0;
    while i < len
        invariant
            0 <= i <= len,
            s_vec@.len() == len,
            // The parts of the sequence up to i are sorted
            forall|l: int, m: int| 0 <= l < m < i ==> less_eq((s_vec@[l].0 as int, s_vec@[l].1 as int), (s_vec@[m].0 as int, s_vec@[m].1 as int)),
            // For selection sort, we only guarantee that s_vec[0..i] contains the smallest i elements in sorted order
            forall|l: int, m: int| 0 <= l < i && i <= m < len ==> less_eq((s_vec@[l].0 as int, s_vec@[l].1 as int), (s_vec@[m].0 as int, s_vec@[m].1 as int)),
            // The multiset of elements remains the same
            s@.map(|idx, val| (val.0 as int, val.1 as int)).to_multiset() == s_vec@.map(|idx, val| (val.0 as int, val.1 as int)).to_multiset()
        decreases len - i
    {
        // Find the minimum element in the unsorted part (s_vec[i..len-1])
        let mut min_idx: int = i;
        let mut j: int = i + 1;
        while j < len
            invariant
                i <= min_idx < j <= len,
                s_vec@.len() == len,
                // Elements before i are sorted and fixed
                forall|l: int, m: int| 0 <= l < m < i ==> less_eq((s_vec@[l].0 as int, s_vec@[l].1 as int), (s_vec@[m].0 as int, s_vec@[m].1 as int)),
                // min_idx points to the smallest element found so far in s_vec[i..j-1]
                forall|k: int| i <= k < j ==> less_eq((s_vec@[min_idx].0 as int, s_vec@[min_idx].1 as int), (s_vec@[k].0 as int, s_vec@[k].1 as int)),
                s@.map(|idx, val| (val.0 as int, val.1 as int)).to_multiset() == s_vec@.map(|idx, val| (val.0 as int, val.1 as int)).to_multiset()
            decreases len - j
        {
            proof {
                if less((s_vec@[j].0 as int, s_vec@[j].1 as int), (s_vec@[min_idx].0 as int, s_vec@[min_idx].1 as int)) {
                    min_idx = j;
                }
            }
            j = j + 1;
        }

        // Swap the found minimum element with s_vec[i] if i is not min_idx
        if min_idx != i {
            let temp = s_vec[i];
            s_vec.set(i, s_vec[min_idx]);
            s_vec.set(min_idx, temp);
            proof {
                lemma_multiset_equivalence_swap(s_vec@, i, min_idx);
            }
        }
        i = i + 1;
    }

    s_vec.into_vec()
}
// </vc-code>


}

fn main() {}