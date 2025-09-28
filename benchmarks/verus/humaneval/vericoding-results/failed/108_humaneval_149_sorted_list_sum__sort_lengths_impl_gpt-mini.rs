// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn comparison(a: Seq<char>, b: Seq<char>, i: int) -> bool
    decreases a.len() - i, b.len() - i
{
    if (i < a.len() && i < b.len()) {
        if a.index(i) < b.index(i) {
            true
        } else if a.index(i) > b.index(i) {
            false
        } else {
            comparison(a, b, i + 1)
        }
    } else {
        if a.len() <= b.len() {
            true
        } else {
            false
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): find index of shortest vector by length */
fn argmin_vecs(v: &Vec<Vec<char>>) -> int
    requires v.len() > 0
    ensures
        0 <= result,
        result < v@.len(),
        forall|i: int| 0 <= i < v@.len() ==> v@.index(result).len() <= v@.index(i).len(),
{
    let mut best: int = 0;
    let mut j: int = 1;
    let len: int = v@.len();
    while j < len
        invariant
            0 <= best,
            best < len,
            1 <= j,
            j <= len,
            forall|i: int| 0 <= i < j ==> v@.index(best).len() <= v@.index(i).len(),
        decreases len - j,
    {
        let bestu = best as usize;
        let ju = j as usize;
        if v[ju].len() < v[bestu].len() {
            best = j;
        }
        j = j + 1;
    }
    best
}
// </vc-helpers>

// <vc-spec>
fn sort_lengths(list: &Vec<Vec<char>>) -> (sorted: Vec<Vec<char>>)
    requires 
        forall|i: int| 0 <= i < list@.len() ==> list@.index(i).len() % 2 == 0
    ensures 
        forall|i: int| 0 <= i < sorted@.len() ==> sorted@.index(i).len() % 2 == 0,
        sorted@.len() == list@.len(),
        sorted@.to_multiset() == list@.to_multiset(),
        forall|x: int, y: int| 0 <= x < y < sorted@.len() ==> sorted@.index(x).len() <= sorted@.index(y).len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): selection by repeatedly removing shortest vector */
    let mut rem = list.clone();
    let mut out: Vec<Vec<char>> = Vec::new();
    while rem.len() > 0
        invariant
            out@.len() + rem@.len() == list@.len(),
            forall|i: int| 0 <= i < out@.len() ==> out@.index(i).len() % 2 == 0,
            forall|i: int, j: int| 0 <= i < out@.len() && 0 <= j < rem@.len() ==> out@.index(i).len() <= rem@.index(j).len(),
        decreases rem@.len(),
    {
        let idx_i = argmin_vecs(&rem);
        let idx = idx_i as usize;
        let v = rem.swap_remove(idx);
        out.push(v);
    }
    out
}
// </vc-code>


}

fn main() {}