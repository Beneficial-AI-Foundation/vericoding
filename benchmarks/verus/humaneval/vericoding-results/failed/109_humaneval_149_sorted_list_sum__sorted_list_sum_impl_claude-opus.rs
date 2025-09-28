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
    /* code modified by LLM (iteration 2): Added decreases clause to while loops */
    let mut result: Vec<Vec<char>> = Vec::new();
    let mut i: usize = 0;
    while i < list.len()
        invariant
            0 <= i <= list.len(),
            result@.len() <= i,
            forall|j: int| 0 <= j < result@.len() ==> result@[j].len() % 2 == 0,
            forall|x: int, y: int| 0 <= x < y < result@.len() ==> result@[x].len() <= result@[y].len(),
            result@.to_multiset().subset_of(list@.take(i as int).to_multiset())
        decreases list.len() - i
    {
        if list[i].len() % 2 == 0 {
            let mut j: usize = 0;
            let mut inserted = false;
            while j < result.len()
                invariant
                    0 <= j <= result.len(),
                    result@.len() <= i,
                    forall|k: int| 0 <= k < result@.len() ==> result@[k].len() % 2 == 0,
                    forall|x: int, y: int| 0 <= x < y < result@.len() ==> result@[x].len() <= result@[y].len(),
                    !inserted ==> forall|k: int| 0 <= k < j ==> result@[k as int].len() < list@[i as int].len()
                decreases result.len() - j
            {
                if !inserted && list[i].len() <= result[j].len() {
                    result.insert(j, list[i].clone());
                    inserted = true;
                    break;
                }
                j = j + 1;
            }
            if !inserted {
                result.push(list[i].clone());
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}