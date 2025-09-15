// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_sorted(v: Seq<i32>) -> bool { forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j] }
// </vc-helpers>

// <vc-spec>
fn insertion_sort(l: Vec<i32>) -> (result: Vec<i32>)
    ensures

        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],

        result@.to_multiset() == l@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): added invariant for for loop to ensure prefix is sorted and multiset preserved */
    let mut result = Vec::new();
    for i in 0..l.len()
        invariant
            i >= 0,
            i <= l.len(),
            result@.len() == i,
            forall|k: int, m: int| 0 <= k < m < i ==> result@[k] <= result@[m],
            result@.take(i).to_multiset() == l@.take(i).to_multiset(),
    {
        let elem = l@.[i];
        let mut j = 0;
        while j < result@.len() && elem > result@[j]
            invariant
                j <= result@.len(),
                forall|k: int| 0 <= k < j ==> result@[k] <= elem,
            decreases result@.len() - j,
        {
            j += 1;
        }
        result.insert(j, elem);
    }
    result
}
// </vc-code>

}
fn main() {}