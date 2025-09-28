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
    /* code modified by LLM (iteration 5): added type annotation for result Vec to fix compilation type inference error */
    let mut result: Vec<Vec<char>> = Vec::new();
    let mut i = 0;
    while i < list.len()
        invariant
            0 <= i as int,
            i as int <= list@.len(),
            result@.len() <= i as int,
            forall|j: int| 0 <= j < result@.len() ==> result@[j].len() % 2 == 0,
            result@.to_multiset().subset_of(list@.to_multiset())
        decreases (list@.len() - i as int)
    {
        if list[i].len() % 2 == 0 {
            result.push(list[i]);
        }
        i += 1;
    }
    if result.len() >= 2 {
        let mut outer = 0;
        while outer < result.len() - 1
            invariant
                0 <= outer as int,
                outer as int <= (result@.len() - 1),
                forall|z: int| 0 <= z < result@.len() ==> result@[z].len() % 2 == 0,
                result@.to_multiset().subset_of(list@.to_multiset()),
                forall|a: int, b: int| 0 <= a < b < outer as int ==> result@[a].len() <= result@[b].len(),
                forall|c: int, d: int| outer as int <= c < d < result@.len() ==> result@[c].len() <= result@[d].len()
            decreases (result@.len() - outer as int)
        {
            let mut min_idx = outer;
            let mut inner = outer + 1;
            while inner < result.len()
                invariant
                    outer as int <= min_idx as int,
                    (min_idx as int) < (inner as int),
                    inner as int <= result@.len(),
                    forall|z: int| outer as int <= z < inner as int ==> result@[(min_idx as int)].len() <= result@[z].len()
                decreases (result@.len() - inner as int)
            {
                if result[inner].len() < result[min_idx].len() {
                    min_idx = inner;
                }
                inner += 1;
            }
            let tmp = result[outer];
            result[outer] = result[min_idx];
            result[min_idx] = tmp;
            outer += 1;
        }
    }
    result
}
// </vc-code>


}

fn main() {}