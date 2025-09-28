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
/* helper modified by LLM (iteration 5): fixed spec function syntax */
spec fn is_sorted_by_length(result: Seq<Vec<char>>) -> bool {
    forall|x: int, y: int| 0 <= x < y < result.len() ==> result.index(x).len() <= result.index(y).len()
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
    /* code modified by LLM (iteration 5): added decreases clause to while loop */
    let mut result: Vec<Vec<char>> = Vec::new();
    let mut i = 0;
    
    while i < list.len()
        invariant
            0 <= i <= list@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@.index(j) == list@.index(j),
            forall|j: int| 0 <= j < i ==> result@.index(j).len() % 2 == 0,
        decreases list@.len() - i
    {
        result.push(list[i].clone());
        i += 1;
    }
    
    let mut j = 0;
    while j < result.len()
        invariant
            0 <= j <= result@.len(),
            result@.len() == list@.len(),
            result@.to_multiset() == list@.to_multiset(),
            forall|k: int| 0 <= k < result@.len() ==> result@.index(k).len() % 2 == 0,
            forall|x: int, y: int| 0 <= x < y < j ==> result@.index(x).len() <= result@.index(y).len(),
        decreases result@.len() - j
    {
        let mut min_idx = j;
        let mut k = j + 1;
        
        while k < result.len()
            invariant
                j <= min_idx < result@.len(),
                j + 1 <= k <= result@.len(),
                forall|m: int| j <= m < k ==> result@.index(min_idx as int).len() <= result@.index(m).len(),
            decreases result@.len() - k
        {
            if result[k].len() < result[min_idx].len() {
                min_idx = k;
            }
            k += 1;
        }
        
        if min_idx != j {
            let temp = result[j].clone();
            result.set(j, result[min_idx].clone());
            result.set(min_idx, temp);
        }
        
        j += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}