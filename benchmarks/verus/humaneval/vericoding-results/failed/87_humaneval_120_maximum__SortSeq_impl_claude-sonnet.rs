// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed proof block from spec function */

// Helper predicate to check if array is sorted in a range
spec fn is_sorted_range(s: Seq<i8>, start: int, end: int) -> bool
{
    forall|i: int, j: int| start <= i < j < end ==> s[i] <= s[j]
}

// Helper predicate to check if an index contains the minimum value in a range
spec fn is_min_in_range(s: Seq<i8>, min_idx: int, start: int, end: int) -> bool
{
    start <= min_idx < end &&
    forall|k: int| start <= k < end ==> s[min_idx] <= s[k]
}

// Helper lemma for preserving multiset after swap
proof fn swap_preserves_multiset(v1: Seq<i8>, v2: Seq<i8>, i: int, j: int)
    requires
        0 <= i < v1.len(),
        0 <= j < v1.len(),
        v1.len() == v2.len(),
        v2[i] == v1[j],
        v2[j] == v1[i],
        forall|k: int| 0 <= k < v1.len() && k != i && k != j ==> v1[k] == v2[k],
    ensures
        v1.to_multiset() == v2.to_multiset(),
{
    assert(v1.to_multiset().count(v1[i]) == v2.to_multiset().count(v1[i]));
    assert(v1.to_multiset().count(v1[j]) == v2.to_multiset().count(v1[j]));
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
    /* code modified by LLM (iteration 5): Simplified implementation without complex proofs */
    let mut result = s.clone();
    let n = result.len();
    
    for i in 0..n
        invariant
            result@.len() == s@.len(),
            s@.to_multiset() == result@.to_multiset(),
            forall|k: int, l: int| 0 <= k < l < (i as int) ==> result@[k] <= result@[l],
    {
        let mut min_idx = i;
        for j in (i + 1)..n
            invariant
                result@.len() == s@.len(),
                s@.to_multiset() == result@.to_multiset(),
                i <= min_idx < n,
                forall|k: int| (i as int) < k < (j as int) ==> result@[min_idx as int] <= result@[k],
        {
            if result[j] < result[min_idx] {
                min_idx = j;
            }
        }
        
        if min_idx != i {
            let temp = result[i];
            result.set(i, result[min_idx]);
            result.set(min_idx, temp);
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}