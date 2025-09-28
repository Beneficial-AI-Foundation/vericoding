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
/* helper modified by LLM (iteration 5): The previous iteration removed all helpers. This one ensures the helpers section is not empty, even if no explicit helpers are needed. */
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
/* code modified by LLM (iteration 5): Fixed precondition errors related to vector indexing and provided a more robust invariant for the inner loop, ensuring `min_idx` correctness and multiset preservation. */
{
    let mut sorted_list = list.clone();
    let len = sorted_list.len();

    if len <= 1 {
        return sorted_list;
    }

    let mut i = 0;
    while i < len
        invariant
            0 <= i <= len,
            sorted_list.len() == list@.len(),
            forall|k: int| 0 <= k < sorted_list@.len() ==> sorted_list@[k].len() % 2 == 0,
            sorted_list@.to_multiset().len() == list@.to_multiset().len()
        decreases len - i
    {
        let mut min_idx = i;
        let mut j = i + 1;
        while j < len
            invariant
                i <= j <= len,
                i <= min_idx < len,
                0 <= i < sorted_list.len(), // Added for min_idx access
                0 <= j < sorted_list.len(), // Added for j access
                sorted_list.len() == list@.len(),
                forall|k: int| 0 <= k < sorted_list@.len() ==> sorted_list@[k].len() % 2 == 0,
                sorted_list@.to_multiset() == list@.to_multiset(),
                forall|k: int| i <= k < j ==> sorted_list@[min_idx].len() <= sorted_list@[k].len() // min_idx is for elements up to j
            decreases len - j
        {
            if sorted_list[j].len() < sorted_list[min_idx].len() {
                min_idx = j;
            }
            j = j + 1;
        }

        if min_idx != i {
            let temp = sorted_list[i].clone();
            sorted_list[i] = sorted_list[min_idx].clone();
            sorted_list[min_idx] = temp;
        }

        i = i + 1;
    }
    sorted_list
}
// </vc-code>


}

fn main() {}