// <vc-preamble>
use vstd::prelude::*;

verus! {

type SortSeqState = Seq<(int, int)>;

spec fn less(a: (int, int), b: (int, int)) -> bool {
    let (x, y) = a;
    let (u, v) = b;
    x < u || (x == u && y > v)
}

spec fn less_eq(a: (int, int), b: (int, int)) -> bool {
    let (x, y) = a;
    let (u, v) = b;
    (x == u && y == v) || less(a, b)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): find minimal index in sequence */
proof fn seq_min_index(vs: Seq<(i8, i8)>) -> int
    requires
        vs.len() > 0,
    ensures
        0 <= result < vs.len(),
        forall|j: int| 0 <= j < vs.len() ==> less_eq((vs@[result].0 as int, vs@[result].1 as int), (vs@[j].0 as int, vs@[j].1 as int)),
{
    let n: int = vs.len();
    let mut min_idx: int = 0;
    let mut i: int = 1;
    while i < n
        invariant
            0 <= min_idx < n,
            1 <= i <= n,
            forall|j: int| 0 <= j < i ==> less_eq((vs@[min_idx].0 as int, vs@[min_idx].1 as int), (vs@[j].0 as int, vs@[j].1 as int)),
        decreases
            n - i,
    {
        if less((vs@[i].0 as int, vs@[i].1 as int), (vs@[min_idx].0 as int, vs@[min_idx].1 as int)) {
            min_idx = i;
        }
        i = i + 1;
    }
    min_idx
}

// </vc-helpers>

// <vc-spec>
fn sort_seq(s: Vec<(i8, i8)>) -> (sorted: Vec<(i8, i8)>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < sorted@.len() ==> less_eq((sorted[i].0 as int, sorted[i].1 as int), (sorted[j].0 as int, sorted[j].1 as int)),
        sorted@.len() == s@.len(),
        s@.map(|i: int, x: (i8, i8)| (x.0 as int, x.1 as int)).to_multiset() == sorted@.map(|i: int, x: (i8, i8)| (x.0 as int, x.1 as int)).to_multiset()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): selection sort using seq_min_index */
    let mut v = s;
    let mut res: Vec<(i8, i8)> = Vec::new();
    while v.len() > 0
        invariant
            res@.len() + v@.len() == s@.len(),
            s@.map(|i: int, x: (i8, i8)| (x.0 as int, x.1 as int)).to_multiset() == (res@ + v@).map(|i: int, x: (i8, i8)| (x.0 as int, x.1 as int)).to_multiset(),
            forall|i: int, j: int| 0 <= i < j < res@.len() ==> less_eq((res@[i].0 as int, res@[i].1 as int), (res@[j].0 as int, res@[j].1 as int)),
        decreases
            v.len(),
    {
        let idx = seq_min_index(v@) as usize;
        res.push(v.swap_remove(idx));
    }
    res
}

// </vc-code>


}

fn main() {}