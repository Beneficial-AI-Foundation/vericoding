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
/* helper modified by LLM (iteration 4): trivial lemma preserving even-length property across vectors */
proof fn even_lengths_stable(sorted: Vec<Vec<char>>)
    requires
        forall|p: int| 0 <= p < sorted@.len() ==> sorted@.index(p).len() % 2 == 0,
    ensures
        forall|p: int| 0 <= p < sorted@.len() ==> sorted@.index(p).len() % 2 == 0,
{
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
    /* code modified by LLM (iteration 4): fixed spec equality between vec and seq; insertion sort by length */
    let n: usize = list.len();
    let mut sorted: Vec<Vec<char>> = Vec::new();

    let mut k: usize = 0;
    while k < n
        invariant
            0 <= (k as int) <= list@.len(),
            sorted@.len() == k as int,
            sorted@.to_multiset() == list@.subrange(0, k as int).to_multiset(),
            forall|p: int| 0 <= p < sorted@.len() ==> sorted@.index(p).len() % 2 == 0,
            forall|x: int, y: int| 0 <= x < y < sorted@.len() ==> sorted@.index(x).len() <= sorted@.index(y).len(),
        decreases list@.len() - (k as int)
    {
        let elem: Vec<char> = list[k].clone();
        proof {
            assert(0 <= (k as int) < list@.len());
            assert(elem@ == list@.index(k as int)@);
        }

        let elem_len: usize = elem.len();
        let mut pos: usize = 0;
        while pos < sorted.len() && sorted[pos].len() <= elem_len
            invariant
                0 <= (pos as int) <= sorted@.len(),
                sorted@.len() == k as int,
                forall|p: int| 0 <= p < sorted@.len() ==> sorted@.index(p).len() % 2 == 0,
                forall|x: int, y: int| 0 <= x < y < sorted@.len() ==> sorted@.index(x).len() <= sorted@.index(y).len(),
                forall|y: int| 0 <= y < (pos as int) ==> sorted@.index(y).len() <= (elem_len as int),
            decreases sorted@.len() - (pos as int)
        {
            pos += 1;
        }

        sorted.insert(pos, elem);
        k += 1;
    }

    sorted
}
// </vc-code>


}

fn main() {}