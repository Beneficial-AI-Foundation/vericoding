// <vc-preamble>
use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;
use vstd::seq_lib::lemma_seq_contains_after_push;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): insert element into a sorted unique vector while preserving order */
fn insert_sorted(acc: Vec<i32>, x: i32) -> (result: Vec<i32>)
    requires
        forall|i: int, j: int| 0 <= i < j < acc.len() ==> acc@[i] < acc@[j],
    ensures
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result@[i] < result@[j],
        forall|i: int| 0 <= i < result.len() ==> acc@.contains(result@[i]) || result@[i] == x,
        forall|i: int| 0 <= i < acc.len() ==> result@.contains(acc@[i]),
{
    let seq_acc = acc@;
    if seq_acc.contains(x) {
        acc
    } else {
        let mut res: Vec<i32> = Vec::new();
        let mut j: int = 0;
        while j < acc.len()
            invariant
                0 <= j <= acc.len(),
            decreases acc.len() - j
        {
            if seq_acc@[j] < x {
                res.push(seq_acc@[j]);
                j += 1;
            } else {
                break;
            }
        }
        res.push(x);
        while j < acc.len()
            invariant
                0 <= j <= acc.len(),
            decreases acc.len() - j
        {
            res.push(seq_acc@[j]);
            j += 1;
        }
        res
    }
}
// </vc-helpers>

// <vc-spec>
fn unique(s: Vec<i32>) -> (result: Vec<i32>)

    ensures
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j],
        forall|i: int| #![auto] 0 <= i < result.len() ==> s@.contains(result[i]),
        forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> result@.contains(s[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): build a sorted list of unique elements by inserting unseen items */
    let mut acc: Vec<i32> = Vec::new();
    let mut i: int = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|k: int| 0 <= k < i ==> acc@.contains(s@[k]),
            forall|p: int, q: int| 0 <= p < q < acc.len() ==> acc@[p] < acc@[q],
        decreases s.len() - i
    {
        let x: i32 = s@[i];
        if !acc@.contains(x) {
            acc = insert_sorted(acc, x);
        }
        i += 1;
    }
    acc
}
// </vc-code>

}
fn main() {}