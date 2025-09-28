// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): converted from proof to exec to allow being called from main function */
fn difference_rec(a: Seq<int>, b: Seq<int>) -> (diff: Seq<int>)
    ensures
        forall|x: int| diff.contains(x) <==> (a.contains(x) && !b.contains(x)),
        forall|i: int, j: int| 0 <= i < j < diff.len() ==> diff.index(i) != diff.index(j),
    decreases a.len()
{
    if a.len() == 0 {
        Seq::empty()
    } else {
        let prev_a = a.subrange(0, a.len() - 1);
        let elem = a.last();
        let prev_diff = difference_rec(prev_a, b);

        if !b.contains(elem) && !prev_diff.contains(elem) {
            proof {
                lemma_push_no_duplicates(prev_diff, elem);
            }
            prev_diff.push(elem)
        } else {
            prev_diff
        }
    }
}

proof fn lemma_push_no_duplicates(s: Seq<int>, e: int)
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s.index(i) != s.index(j),
        !s.contains(e),
    ensures
        forall|i: int, j: int| 0 <= i < j < s.push(e).len() ==> s.push(e).index(i) != s.push(e).index(j),
{
}
// </vc-helpers>

// <vc-spec>
fn difference(a: Seq<int>, b: Seq<int>) -> (diff: Seq<int>)
    ensures
        forall|x: int| diff.contains(x) <==> (a.contains(x) && !b.contains(x)),
        forall|i: int, j: int| 0 <= i < j < diff.len() ==> diff.index(i) != diff.index(j),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): called the new executable recursive helper function */
    difference_rec(a, b)
}
// </vc-code>

}
fn main() {}