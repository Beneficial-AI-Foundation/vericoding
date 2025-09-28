// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_sorted(seq: Seq<i8>) -> bool {
    forall |i: int, j: int| 0 <= i < j < seq.len() ==> seq[i] <= seq[j]
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
{
    /* code modified by LLM (iteration 5): Fixed type mismatch for LENGTH changed to nat, and removed .old() by introducing ghost variable orig_sorted in inner loop invariant to properly track unmodified prefixes. */
    let length: usize = s.len();
    let LENGTH: nat = s@.len();
    let mut sorted: Vec<i8> = Vec::new();
    let mut init_counter: usize = 0;
    while init_counter < length
        invariant
            0 <= (init_counter as int) <= LENGTH,
            sorted@.len() == (init_counter as int),
            forall |k: int| 0 <= k < (init_counter as int) ==> sorted@[k] == s@[k],
    {
        sorted.push(s[init_counter]);
        init_counter += 1;
    }
    let mut i: usize = 1;
    while i < length
        invariant
            1 <= (i as int) <= LENGTH,
            sorted@.len() == LENGTH,
            s@.to_multiset() == sorted@.to_multiset(),
            is_sorted(sorted@.take(i as int)),
    {
        let key = sorted[i];
        let orig_sorted = Ghost(sorted@);
        let mut j: usize = i;
        while j > 0 && sorted[j - 1] > key
            invariant
                i >= j,
                0 <= (j as int) <= (i as int),
                s@.to_multiset() == sorted@.to_multiset(),
                forall |k: int| 0 <= k < (j as int) ==> sorted@[k] == orig_sorted@[k],
                sorted@.take(j as int + 1) == orig_sorted@.take(j as int).push(key),
                sorted@[j as int] == key,
        {
            sorted[j] = sorted[j - 1];
            sorted[j - 1] = key;
            j -= 1;
        }
        i += 1;
    }
    sorted
}
// </vc-code>


}

fn main() {}