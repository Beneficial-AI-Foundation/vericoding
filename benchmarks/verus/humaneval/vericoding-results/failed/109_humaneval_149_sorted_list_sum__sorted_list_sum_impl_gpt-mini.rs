// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn comparison(a: Seq<char>, b: Seq<char>, i: int) -> bool
    recommends 0 <= i <= a.len() && 0 <= i <= b.len()
    decreases a.len() - i, b.len() - i
{
    if (i < a.len() && i < b.len()) {
        if a[i] < b[i] {
            true
        } else if a[i] > b[i] {
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
/* helper modified by LLM (iteration 3): predicate for even-length sequence */
spec fn seq_even_len(s: Seq<char>) -> bool {
    s.len() % 2 == 0
}
// </vc-helpers>

// <vc-spec>
fn sorted_list_sum(list: Vec<Vec<char>>) -> (sorted: Vec<Vec<char>>)
    requires 
        list@.len() > 0
    ensures 
        sorted@.len() <= list@.len(),
        forall|i: int| 0 <= i < sorted@.len() ==> sorted@[i].len() % 2 == 0,
        forall|x: int, y: int| 0 <= x < y < sorted@.len() ==> sorted@[x].len() <= sorted@[y].len(),
        sorted@.to_multiset().subset_of(list@.to_multiset())
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): filter even-length sequences then selection by repeated swap_remove */
    let mut res: Vec<Vec<char>> = Vec::new();
    let mut i: usize = 0;
    while i < list.len()
        invariant
            i <= list.len(),
        decreases list.len() - i
    {
        let item: Vec<char> = list[i].clone();
        if item.len() % 2 == 0 {
            res.push(item);
        }
        i += 1;
    }

    let mut sorted: Vec<Vec<char>> = Vec::new();
    while res.len() > 0
        invariant
            sorted.len() <= list.len(),
        decreases res.len()
    {
        let mut min_idx: usize = 0;
        let mut k: usize = 1;
        while k < res.len()
            invariant
                k <= res.len(),
            decreases res.len() - k
        {
            if res[k].len() < res[min_idx].len() {
                min_idx = k;
            }
            k += 1;
        }

        let elem: Vec<char> = res.swap_remove(min_idx);
        sorted.push(elem);
    }

    sorted
}
// </vc-code>


}

fn main() {}