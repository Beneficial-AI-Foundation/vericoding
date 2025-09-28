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
    /* code modified by LLM (iteration 5): Fixed bubble sort invariants and logic */
    let mut sorted = list.clone();
    let n = sorted.len();
    
    if n == 0 {
        return sorted;
    }
    
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == sorted.len(),
            sorted@.to_multiset() == list@.to_multiset(),
            forall|k: int| 0 <= k < sorted@.len() ==> sorted@.index(k).len() % 2 == 0,
            forall|x: int, y: int| n - i <= x < y < n ==> sorted@.index(x).len() <= sorted@.index(y).len(),
            forall|x: int, y: int| 0 <= x < n - i && n - i < y < n ==> sorted@.index(x).len() <= sorted@.index(y).len(),
        decreases n - i
    {
        if i == n - 1 {
            i = i + 1;
            continue;
        }
        
        let mut j: usize = 0;
        while j < n - i - 1
            invariant
                0 <= j <= n - i - 1,
                0 <= i < n,
                n == sorted.len(),
                sorted@.to_multiset() == list@.to_multiset(),
                forall|k: int| 0 <= k < sorted@.len() ==> sorted@.index(k).len() % 2 == 0,
                forall|x: int, y: int| n - i <= x < y < n ==> sorted@.index(x).len() <= sorted@.index(y).len(),
                forall|x: int, y: int| 0 <= x < n - i && n - i < y < n ==> sorted@.index(x).len() <= sorted@.index(y).len(),
                forall|k: int| 0 <= k < j ==> sorted@.index(k).len() <= sorted@.index(j as int).len(),
            decreases n - i - 1 - j
        {
            if sorted[j].len() > sorted[j + 1].len() {
                let temp = sorted[j].clone();
                sorted.set(j, sorted[j + 1].clone());
                sorted.set(j + 1, temp);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    sorted
}
// </vc-code>


}

fn main() {}