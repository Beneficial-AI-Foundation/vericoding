// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn sort_seq(s: Vec<i8>) -> (sorted: Vec<i8>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < sorted@.len() ==> sorted@[i] <= sorted@[j],
        sorted@.len() == s@.len(),
        s@.to_multiset() == sorted@.to_multiset()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed invalid old() expressions with &mut and type annotations, replaced with direct s@ for original length and multiset, and used old(result) for inner loop snapshots */
    let mut result = s;
    let len = result.len();

    let mut i = 1;
    while i < len
        invariant
            i <= len,
            forall |m: int, n: int| 0 <= m < n < i ==> result@[m] <= result@[n],
            result@.len() == s@.len(),
            result@.to_multiset() == s@.to_multiset(),
    {
        let curr = result[i];
        let mut j = i;

        while j > 0 && result[j - 1] > curr
            invariant
                0 <= j <= i,
                forall |p: int, q: int| 0 <= p < q < j ==> result@[p] <= result@[q],
                forall |p: int, q: int| j <= p < q < len ==> result@[p] <= result@[q],
                forall |p: int| 0 <= p < len && p != j ==> result@[p] == old(result)@[p],
                result@.len() == s@.len(),
                result@.to_multiset() == s@.to_multiset(),
        {
            result.set(j, result[j - 1]);
            j -= 1;
        }

        result.set(j, curr);
        i += 1;
    }

    result
}
// </vc-code>


}

fn main() {}