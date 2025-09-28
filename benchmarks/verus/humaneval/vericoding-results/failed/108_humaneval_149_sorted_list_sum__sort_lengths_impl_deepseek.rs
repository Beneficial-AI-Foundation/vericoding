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
/* helper modified by LLM (iteration 5): Add bubble_sort_pass helper function */
fn bubble_sort_pass(list: &mut Vec<Vec<char>>, pass: usize)
    requires
        old(list)@.len() % 2 == 0,
        pass < old(list)@.len(),
        forall|i: int| 0 <= i < old(list)@.len() ==> old(list)@.index(i).len() % 2 == 0
    ensures
        list@.len() == old(list)@.len(),
        list@.to_multiset() == old(list)@.to_multiset(),
        forall|i: int| 0 <= i < list@.len() ==> list@.index(i).len() % 2 == 0,
        forall|j: int| 0 <= j < pass ==> list@.index(j).len() <= list@.index(j + 1).len()
{
    let mut i = pass;
    while i < list.len() - 1
        invariant
            0 <= i <= list@.len() - 1,
            list@.len() == old(list)@.len(),
            list@.to_multiset() == old(list)@.to_multiset(),
            forall|k: int| 0 <= k < list@.len() ==> list@.index(k).len() % 2 == 0,
            forall|j: int| 0 <= j < pass ==> list@.index(j).len() <= list@.index(j + 1).len(),
            forall|j: int| pass <= j < i ==> list@.index(j).len() <= list@.index(j + 1).len()
        decreases list@.len() - 1 - i
    {
        if list[i].len() > list[i + 1].len() {
            let temp = list[i].clone();
            list.set(i, list[i + 1].clone());
            list.set(i + 1, temp);
        }
        i = i + 1;
    }
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
/* code modified by LLM (iteration 5): Remove bubble_sort_pass call and implement sorting loop directly */
{
    let mut sorted = list.clone();
    let mut pass = 0;
    
    while pass < sorted.len()
        invariant 
            0 <= pass <= sorted@.len(),
            forall|i: int| 0 <= i < sorted@.len() ==> sorted@.index(i).len() % 2 == 0,
            sorted@.len() == list@.len(),
            sorted@.to_multiset() == list@.to_multiset()
        decreases sorted@.len() - pass
    {
        let mut i = pass;
        while i < sorted.len() - 1
            invariant
                0 <= i <= sorted@.len() - 1,
                forall|j: int| 0 <= j < sorted@.len() ==> sorted@.index(j).len() % 2 == 0,
                sorted@.len() == list@.len(),
                sorted@.to_multiset() == list@.to_multiset()
            decreases sorted@.len() - 1 - i
        {
            if sorted[i].len() > sorted[i + 1].len() {
                let temp = sorted[i].clone();
                sorted.set(i, sorted[i + 1].clone());
                sorted.set(i + 1, temp);
            }
            i = i + 1;
        }
        pass = pass + 1;
    }
    
    proof {
        assert(forall|i: int| 0 <= i < sorted@.len() - 1 ==> sorted@.index(i).len() <= sorted@.index(i + 1).len());
    }
    sorted
}
// </vc-code>


}

fn main() {}