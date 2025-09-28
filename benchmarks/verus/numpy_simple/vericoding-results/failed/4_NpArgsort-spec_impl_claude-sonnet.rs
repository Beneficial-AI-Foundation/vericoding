// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type mismatches using proper casting and sequence indexing */
spec fn is_permutation(result: Seq<usize>, n: nat) -> bool {
    result.len() == n &&
    forall|i: nat| i < n ==> exists|j: nat| j < n && result[j as int] == i
}

spec fn is_sorted_by_values(result: Seq<usize>, a: Seq<i8>) -> bool {
    forall|i: int, j: int| 0 <= i < j < result.len() ==> a[result[i] as int] <= a[result[j] as int]
}
// </vc-helpers>

// <vc-spec>
fn argsort(a: Vec<i8>) -> (result: Vec<usize>)
    ensures 
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] a@[result@[i] as int] <= #[trigger] a@[result@[j] as int],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation errors by avoiding cast operations outside ghost code */
    let n = a.len();
    let mut result: Vec<usize> = Vec::new();
    
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result@[k] == k,
    {
        result.push(i);
        i += 1;
    }
    
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            result.len() == n,
            forall|k: int| 0 <= k < n ==> result@.contains(k as usize),
            forall|p: int, q: int| 0 <= p < q < i ==> a@[result@[p]] <= a@[result@[q]],
    {
        let mut j = i + 1;
        while j < n
            invariant
                i < j <= n,
                result.len() == n,
                forall|k: int| 0 <= k < n ==> result@.contains(k as usize),
                forall|p: int, q: int| 0 <= p < q < i ==> a@[result@[p]] <= a@[result@[q]],
                forall|k: int| i < k < j ==> a@[result@[i]] <= a@[result@[k]],
        {
            if a@[result@[j]] < a@[result@[i]] {
                let temp = result@[i];
                result.set(i, result@[j]);
                result.set(j, temp);
            }
            j += 1;
        }
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}