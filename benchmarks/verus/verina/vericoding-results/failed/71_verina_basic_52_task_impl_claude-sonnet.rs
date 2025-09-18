// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// Helper predicate to check if a vector is sorted
spec fn is_sorted(v: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j]
}

/* helper modified by LLM (iteration 5): added actual proof body using swap properties */
proof fn lemma_swap_preserves_multiset(v1: Seq<i32>, v2: Seq<i32>, i: int, j: int)
    requires
        0 <= i < v1.len(),
        0 <= j < v1.len(),
        v2.len() == v1.len(),
        v2[i] == v1[j],
        v2[j] == v1[i],
        forall|k: int| 0 <= k < v1.len() && k != i && k != j ==> v2[k] == v1[k],
    ensures
        v1.to_multiset() == v2.to_multiset(),
{
    assert(v2 =~= v1.update(i, v1[j]).update(j, v1[i]));
}
// </vc-helpers>

// <vc-spec>
fn bubble_sort(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        a@.to_multiset() == result@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed bounds checks and invariants */
    let mut result = a.clone();
    let n = result.len();
    
    for i in 0..n
        invariant
            result.len() == a.len(),
            a@.to_multiset() == result@.to_multiset(),
            forall|x: int, y: int| 0 <= x < y < i ==> result@[x] <= result@[y],
    {
        for j in 0..(n - i - 1)
            invariant
                result.len() == a.len(),
                a@.to_multiset() == result@.to_multiset(),
                forall|x: int, y: int| 0 <= x < y < i ==> result@[x] <= result@[y],
                j < result.len(),
                j + 1 < result.len(),
        {
            if result[j] > result[j + 1] {
                proof {
                    let old_seq = result@;
                    let new_seq = old_seq.update(j as int, old_seq[j as int + 1]).update(j as int + 1, old_seq[j as int]);
                    lemma_swap_preserves_multiset(old_seq, new_seq, j as int, j as int + 1);
                }
                let temp = result[j];
                result.set(j, result[j + 1]);
                result.set(j + 1, temp);
            }
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}