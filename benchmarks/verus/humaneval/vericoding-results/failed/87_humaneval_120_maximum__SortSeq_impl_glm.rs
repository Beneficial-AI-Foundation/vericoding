// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed type mismatches by converting usize to int in requires conditions */
fn insert_into_sorted(sorted: &mut Vec<i8>, x: i8, pos: usize)
    requires 
        forall|i: int, j: int| 0 <= i < j < sorted@.len() ==> sorted@[i] <= sorted@[j],
        0 <= (pos as int) <= sorted@.len(),
        forall|i: int| 0 <= i < (pos as int) ==> sorted@[i] < x,
        (pos as int) < sorted@.len() ==> sorted@[pos as int] >= x,
    ensures
        forall|i: int, j: int| 0 <= i < j < sorted@.len() ==> sorted@[i] <= sorted@[j],
        sorted@.len() == old(sorted)@.len() + 1,
        sorted@.to_multiset() == old(sorted)@.to_multiset().insert(x),
{
    sorted.insert(pos, x);
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
    /* code modified by LLM (iteration 4): fixed slice syntax by using subrange method */
    let mut sorted: Vec<i8> = Vec::new();
    for i in 0..s.len()
        invariant
            forall|k: int, l: int| 0 <= k < l < sorted@.len() ==> sorted@[k] <= sorted@[l],
            sorted@.len() == i,
            sorted@.to_multiset() == s@.subrange(0, i as int).to_multiset()
    {
        let x = s[i];
        let mut j = 0;
        while j < sorted.len() && sorted[j] < x
            invariant
                0 <= (j as int) <= sorted@.len(),
                forall|k: int| 0 <= k < (j as int) ==> sorted@[k] < x,
        {
            j += 1;
        }
        insert_into_sorted(&mut sorted, x, j);
    }
    sorted
}
// </vc-code>


}

fn main() {}