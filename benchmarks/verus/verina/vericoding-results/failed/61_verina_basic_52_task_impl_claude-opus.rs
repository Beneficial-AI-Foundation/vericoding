// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 3): Added decreases clauses to both loops */
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
            a@.to_multiset() == result@.to_multiset(),
            forall|k: int, l: int| (n - i) <= k < l < n ==> result[k] <= result[l],
            forall|k: int| (n - i - 1) < k < n ==> forall|l: int| 0 <= l <= k ==> result[l] <= result[k],
        decreases n - i
    {
        let mut j: usize = 0;
        while j < n - i - 1
            invariant
                j < n,
                i + j < n,
                n - i - 1 < n,
                result.len() == n,
                a@.to_multiset() == result@.to_multiset(),
                forall|k: int, l: int| (n - i) <= k < l < n ==> result[k] <= result[l],
                forall|k: int| (n - i - 1) < k < n ==> forall|l: int| 0 <= l <= k ==> result[l] <= result[k],
                forall|k: int| 0 <= k <= j ==> result[k] <= result[n - i - 1],
            decreases n - i - 1 - j
        {
            if result[j] > result[j + 1] {
                let temp = result[j];
                result.set(j, result[j + 1]);
                result.set(j + 1, temp);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}