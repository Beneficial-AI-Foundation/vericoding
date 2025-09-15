// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added trigger annotations to is_sorted predicate */
spec fn is_sorted(v: Seq<i32>) -> bool {
    forall|i: int, j: int| #[trigger] (0 <= i < j < v.len()) ==> #[trigger] (v[i] <= v[j])
}

proof fn swap_preserves_multiset(v: &Vec<i32>, i: usize, j: usize, result: &Vec<i32>)
    requires
        i < v.len(),
        j < v.len(),
        result.len() == v.len(),
        forall|k: int| 0 <= k < v.len() && k != i as int && k != j as int ==> result[k] == v[k],
        result[i as int] == v[j as int],
        result[j as int] == v[i as int],
    ensures
        v@.to_multiset() == result@.to_multiset(),
{
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
/* code modified by LLM (iteration 5): Added trigger annotations to quantifiers in invariants */
{
    let mut result = a.clone();
    let n = result.len();
    
    if n == 0 {
        return result;
    }
    
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == a.len(),
            result.len() == n,
            i <= n,
            forall|k: int, l: int| 0 <= k < l < i ==> result[k] <= result[l],
            forall|k: int| #[trigger] (0 <= k < i) ==> forall|l: int| #[trigger] (i <= l < n) ==> result[k] <= result[l],
            a@.to_multiset() == result@.to_multiset(),
        decreases n - i
    {
        let mut j: usize = n - 1;
        while j > i
            invariant
                result.len() == a.len(),
                result.len() == n,
                i < n,
                i <= j < n,
                forall|k: int, l: int| 0 <= k < l < i ==> result[k] <= result[l],
                forall|k: int| #[trigger] (0 <= k < i) ==> forall|l: int| #[trigger] (i <= l < n) ==> result[k] <= result[l],
                forall|k: int| j < k < n ==> result[j as int] <= result[k],
                a@.to_multiset() == result@.to_multiset(),
            decreases j - i
        {
            if result[j - 1] > result[j] {
                let temp = result[j - 1];
                let mut new_result = result.clone();
                new_result.set(j - 1, result[j]);
                new_result.set(j, temp);
                proof {
                    let prev_j = (j - 1) as usize;
                    swap_preserves_multiset(&result, prev_j, j, &new_result);
                }
                result = new_result;
            }
            j = j - 1;
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}