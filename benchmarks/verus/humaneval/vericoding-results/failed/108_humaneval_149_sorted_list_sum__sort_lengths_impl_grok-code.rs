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
    /* code modified by LLM (iteration 5): Added decreases clause to outer while loop */
    let mut result: Vec<Vec<char>> = Vec::new();
    let mut i: usize = 0;
    let n = list.len();
    while i < n
        invariant
            i <= n,
            result@.len() == i as int,
            result@.to_multiset() == list@.subrange(0, i as int).to_multiset(),
            forall|j: int| 0 <= j < (i as int) ==> result@.index(j).len() % 2 == 0,
            forall|j: int| 0 <= j + 1 < (i as int) ==> result@.index(j).len() <= result@.index(j + 1).len()
        decreases (n as int) - (i as int)
    {
        let item = list[i].clone();
        let mut pos: usize = 0;
        while pos < result.len() && result[pos].len() <= item.len()
            invariant
                pos <= (result@.len() as int),
                forall|k: int| 0 <= k < (pos as int) ==> result@[k].len() as int <= item@.len() as int
            decreases (result@.len() as int) - (pos as int)
        {
            pos = pos + 1;
        }
        result.insert(pos, item);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}