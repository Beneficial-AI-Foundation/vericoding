// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn msort(a: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] as int <= result[j] as int,
        result@.to_multiset() =~= a@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed syntax errors in variable names, Unicode quotes, and added @ for Vec indexing in invariants */
    if a.len() <= 1 {
        return a;
    }
    let mut result = a;
    let mut i = 1;
    while i < result.len()
        invariant
            1 <= i <= result.len(),
            0 <= i - 1 < result.len(),
            forall|p: int, q: int| 0 <= p < q < i ==> result@[p] <= result@[q],
            result@.to_multiset() =~= a@.to_multiset()
        decreases result.len() - i
    {
        let key = result@[i];
        let mut j = i;
        while j > 0 && result@[j - 1] > key
            invariant
                0 < j <= i,
                0 <= j - 1 < result.len(),
                result@.to_multiset() =~= a@.to_multiset()
            decreases j
        {
            result.set(j, result@[j - 1]);
            j -= 1;
        }
        result.set(j, key);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}