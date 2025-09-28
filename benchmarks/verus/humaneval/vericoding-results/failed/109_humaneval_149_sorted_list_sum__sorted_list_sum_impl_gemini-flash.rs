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
        /* code modified by LLM (iteration 5): Corrected `while` loop invariant for `min_idx` to prevent an out-of-bounds error. */
        let mut result: Vec<Vec<char>> = Vec::new();
        let mut i = 0;

        while i < list.len()
            invariant
                0 <= i as int <= list.len(),
                result@.to_multiset().subset_of(list@.to_multiset()),
                forall|k: int| 0 <= k < result@.len() ==> result@[k].len() % 2 == 0,
        {
            if list.get(i).is_Some() && list.get(i).unwrap().len() % 2 == 0 {
                result.push(list.get(i).unwrap().clone());
            }
            i = i + 1;
        }

        // Selection sort based on length (ascending)
        let mut j = 0;
        while j < result.len()
            invariant
                0 <= j as int <= result.len(),
                result@.to_multiset().subset_of(list@.to_multiset()),
                forall|k: int| 0 <= k < result@.len() ==> result@[k].len() % 2 == 0,
                forall|x: int, y: int| 0 <= x < y < j ==> result@[x].len() <= result@[y].len(),
        {
            let mut min_idx = j;
            let mut k = j + 1;
            while k < result.len()
                invariant
                    j <= min_idx as int,
                    min_idx as int < result.len(), // Needs to be less than, not less than or equal to.
                    j <= k as int,
                    k as int <= result.len(),
                    result@.to_multiset().subset_of(list@.to_multiset()),
                    forall|idx: int| 0 <= idx < result.len() ==> result@[idx].len() % 2 == 0,
                    forall|idx: int| j <= idx < k ==> result@[min_idx].len() <= result@[idx].len(),
            {
                if result.get(k).is_Some() && result.get(min_idx).is_Some() && result.get(k).unwrap().len() < result.get(min_idx).unwrap().len() {
                    min_idx = k;
                }
                k = k + 1;
            }
            if min_idx != j {
                let temp = result.swap_remove(min_idx);
                result.insert(j, temp);
            }
            j = j + 1;
        }
        result
    }
// </vc-code>


}

fn main() {}