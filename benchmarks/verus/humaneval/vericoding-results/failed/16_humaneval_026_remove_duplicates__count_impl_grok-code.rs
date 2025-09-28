// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_rec(a: Seq<int>, x: int) -> int
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        count_rec(a.subrange(1, a.len() as int), x) + (if a[0] == x { 1 as int } else { 0 as int })
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added decreases clause to recursive spec function */
spec fn seq_count(s: Seq<int>, x: int) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        seq_count(s.subrange(1, s.len() as int), x) + if s[0] == x { 1 as int } else { 0 as int }
    }
}

proof fn lemma_seq_count_subrange(s: Seq<int>, x: int, low: int, high: int)
    requires 0 <= low <= high <= s.len()
    ensures seq_count(s.subrange(low, high), x) == count_rec(s.subrange(low, high), x)
{
    if low < high {
        lemma_seq_count_subrange(s, x, low + 1, high);
    }
}
// </vc-helpers>

// <vc-spec>
fn count(a: Vec<i8>, x: i8) -> (cnt: i8)
    ensures 
        cnt as int == count_rec(a@.map(|i: int, v: i8| v as int), x as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Rechecked proof for consistency with updated helpers */
{
    let mut i: usize = 0;
    let mut cnt: i8 = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            cnt as int == count_rec(a@.subrange(0, i as int).map(|i: int, v: i8| v as int), x as int)
        decreases a.len() - i
    {
        proof {
            if a@[i as int] == x {
                lemma_seq_count_subrange(a@.map(|i: int, v: i8| v as int), x as int, 0, i as int + 1);
                lemma_seq_count_subrange(a@.map(|i: int, v: i8| v as int), x as int, i as int + 1, a.len() as int);
                assert(cnt as int == count_rec(a@.subrange(0, i as int).map(|i: int, v: i8| v as int), x as int));
            } else {
                assert(cnt as int == count_rec(a@.subrange(0, i as int).map(|i: int, v: i8| v as int), x as int));
            }
        }
        if a[i] == x {
            cnt = cnt + 1;
        }
        i = i + 1;
    }
    return cnt;
}
// </vc-code>


}

fn main() {}