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
/* helper modified by LLM (iteration 4): fixed nat type casting and operations */
fn int_to_usize(i: int) -> usize
    requires 0 <= i
    ensures i == int_to_usize(i) as int
{
    i as usize
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
/* code modified by LLM (iteration 4): converted nat indices to int and fixed type operations */
{
    let mut sorted: Vec<Vec<char>> = list.clone();
    let mut i: int = 0;
    while i < sorted@.len()
        invariant
            0 <= i <= sorted@.len(),
            sorted@.to_multiset() == list@.to_multiset(),
            forall|x: int, y: int| 0 <= x < y < i ==> sorted@.index(x).len() <= sorted@.index(y).len(),
            forall|k: int| i <= k < sorted@.len() ==> forall|l: int| 0 <= l < i ==> sorted@.index(l).len() <= sorted@.index(k).len(),
        decreases sorted@.len() - i
    {
        let mut min_index: int = i;
        let mut j: int = i + 1;
        while j < sorted@.len()
            invariant
                i <= min_index < sorted@.len(),
                i < j <= sorted@.len(),
                forall|k: int| i <= k < j ==> sorted@[min_index].len() <= sorted@[k].len(),
            decreases sorted@.len() - j
        {
            if sorted[int_to_usize(j)].len() < sorted[int_to_usize(min_index)].len() {
                min_index = j;
            }
            j = j + 1;
        }
        sorted.swap(int_to_usize(i), int_to_usize(min_index));
        i = i + 1;
    }
    sorted
}
// </vc-code>


}

fn main() {}