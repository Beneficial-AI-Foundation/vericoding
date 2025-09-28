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
    /* code modified by LLM (iteration 5): Added decreases clause to inner while loop to ensure termination */
    let mut v = a.clone();
    let mut n = v.len();
    while n > 1
        invariant
            v@.len() == a.len(),
            a@.to_multiset() == v@.to_multiset(),
            forall|i: int| 0 <= i < n <= v@.len() ==> v@[i] <= v@[n - 1]
        decreases n
    {
        let mut i = 0;
        while i < n - 1
            invariant
                0 <= i <= n - 1,
                v@.len() == a.len(),
                a@.to_multiset() == v@.to_multiset()
            decreases n - i - 1
        {
            if v[i] > v[i + 1] {
                let temp = v[i];
                v[i] = v[i + 1];
                v[i + 1] = temp;
            }
            i = i + 1;
        }
        n = n - 1;
    }
    v
}
// </vc-code>

}
fn main() {}