// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_sorted(v: Vec<i32>) -> bool
{
    forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j]
}

spec fn swap_preserves_multiset(v1: Vec<i32>, v2: Vec<i32>, i: usize, j: usize) -> bool
{
    v1.len() == v2.len() &&
    i < v1.len() &&
    j < v1.len() &&
    v2[i as int] == v1[j as int] &&
    v2[j as int] == v1[i as int] &&
    (forall|k: int| 0 <= k < v1.len() && k != i && k != j ==> v1[k] == v2[k])
}

/* helper modified by LLM (iteration 5): fix proof implementation with proper multiset reasoning */
proof fn swap_maintains_multiset(v1: Vec<i32>, v2: Vec<i32>, i: usize, j: usize)
    requires swap_preserves_multiset(v1, v2, i, j)
    ensures v1@.to_multiset() == v2@.to_multiset()
{
    assert(v1@.to_multiset().remove(v1[i as int]).insert(v1[j as int]) == v1@.to_multiset());
    assert(v2@.to_multiset().remove(v2[j as int]).insert(v2[i as int]) == v2@.to_multiset());
}

spec fn partially_sorted(v: Vec<i32>, end: usize) -> bool
{
    forall|i: int, j: int| end <= i < j < v.len() ==> v[i] <= v[j]
}

spec fn bubble_pass_complete(v: Vec<i32>, pass: usize) -> bool
{
    forall|i: int, j: int| pass <= i < j < v.len() ==> v[i] <= v[j]
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
    /* code modified by LLM (iteration 5): fix trigger annotation for quantifier */
    let mut result = a.clone();
    let n = result.len();
    
    for i in 0..n
        invariant
            result.len() == a.len(),
            result@.to_multiset() == a@.to_multiset(),
            forall|k: int, l: int| (n - i) <= k < l < result.len() ==> result[k] <= result[l]
    {
        for j in 0..(n - i - 1)
            invariant
                result.len() == a.len(),
                result@.to_multiset() == a@.to_multiset(),
                forall|k: int, l: int| (n - i) <= k < l < result.len() ==> result[k] <= result[l],
                forall|k: int| 0 <= k <= j && k + 1 < result.len() && k < (n - i - 1) ==> #[trigger] result[k] <= result[k + 1],
                j < n - i - 1,
                j + 1 < result.len()
        {
            if j + 1 < result.len() && result[j] > result[j + 1] {
                let temp1 = result[j];
                let temp2 = result[j + 1];
                result.set(j, temp2);
                result.set(j + 1, temp1);
            }
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}