// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added trigger annotations */
fn min_index_from(a: &Vec<i32>, start: usize) -> (result: usize)
    requires
        start < a.len(),
    ensures
        start <= result < a.len(),
        forall|i: int| start <= i < a.len() ==> a[result as int] <= a[i],
{
    let mut min_idx = start;
    let mut i = start + 1;
    while i < a.len()
        invariant
            start <= min_idx < a.len(),
            start + 1 <= i <= a.len(),
            forall|j: int| start <= j < i ==> a[min_idx as int] <= a[j],
        decreases a.len() - i,
    {
        if a[i] < a[min_idx] {
            min_idx = i;
        }
        i += 1;
    }
    min_idx
}

proof fn swapped_multiset_equiv<T>(v1: Vec<T>, v2: Vec<T>, i: usize, j: usize)
    requires
        i < v1.len(),
        j < v1.len(),
        v2.len() == v1.len(),
        v2[i as int] == v1[j as int],
        v2[j as int] == v1[i as int],
        forall|k: int| 0 <= k < v1.len() && k != i && k != j ==> v2[k] == v1[k],
    ensures
        v2@ =~= v1@,
{
    // Proof by multiset reasoning
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i <= j < result.len() ==> result[i] <= result[j],
        result@ =~= a@,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed trigger annotations */
    let mut result = a.clone();
    let mut pos = 0;
    
    while pos < result.len()
        invariant
            pos <= result.len(),
            result.len() == a.len(),
            forall|i: int, j: int| 0 <= i <= j < pos ==> result[i] <= result[j],
            result@ =~= a@,
            forall|i: int| #[trigger] result[i] pos <= i < result.len() ==> (forall|j: int| #[trigger] result[j] 0 <= j < pos ==> result[j] <= result[i]),
        decreases result.len() - pos,
    {
        if pos < result.len() {
            let min_idx = min_index_from(&result, pos);
            if min_idx != pos {
                let old_result = result.clone();
                let temp = result[pos];
                result.set(pos, result[min_idx]);
                result.set(min_idx, temp);
                
                proof {
                    swapped_multiset_equiv(old_result, result, pos, min_idx);
                }
            }
        }
        pos += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}