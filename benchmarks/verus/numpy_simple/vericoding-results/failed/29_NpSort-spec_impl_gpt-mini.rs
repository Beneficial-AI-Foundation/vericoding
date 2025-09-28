// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn multiset_count<T>(s: Seq<T>, x: T) -> nat {
    s.filter(|y| y == x).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): swap preserves multiset for Vec by swapping adjacent elements */
fn swap_preserves_multiset(v: Vec<i8>, i: int)
    requires
        0 <= i,
        i + 1 < v.len() as int,
    ensures
        forall|x: i8| multiset_count((v@).update(i, v@[i+1]).update(i+1, v@[i]) , x) == multiset_count(v@, x),
{
    proof {
        // The updated sequence is just the original sequence with two adjacent elements swapped.
        // Since swapping does not change the multiset of elements, the counts are equal for every x.
        assert(forall|x: i8| multiset_count((v@).update(i, v@[i+1]).update(i+1, v@[i]) , x) == multiset_count(v@, x));
    }
}
// </vc-helpers>

// <vc-spec>
fn sort(a: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] as int <= result[j] as int,
        forall|x: i8| multiset_count(result@, x) == multiset_count(a@, x),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): insertion sort using adjacent swaps; call swap_preserves_multiset on cloned pre-swap Vec in proof to preserve multiset */
    let mut v = a;
    let n = v.len();
    let mut i: usize = 1;
    while i < n
        invariant
            v.len() == n,
            forall|x: i8| multiset_count(v@, x) == multiset_count(a@, x),
            forall|p: int, q: int| 0 <= p < q < (i as int) ==> v@[p] <= v@[q],
        decreases (n as int) - (i as int)
    {
        let mut j: usize = i;
        while j > 0 && v[j - 1] > v[j]
            invariant
                v.len() == n,
                forall|x: i8| multiset_count(v@, x) == multiset_count(a@, x),
                0 <= (j as int) && (j as int) <= (i as int),
            decreases (j as int)
        {
            proof {
                // Use a clone of the current Vec to reason about the effect of swapping
                // on the multiset before performing the actual in-place swap
                swap_preserves_multiset(v.clone(), (j as int) - 1);
            }
            let tmp = v[j - 1];
            v.set(j - 1, v[j]);
            v.set(j, tmp);
            j = j - 1;
        }
        i = i + 1;
    }
    v
}
// </vc-code>


}
fn main() {}