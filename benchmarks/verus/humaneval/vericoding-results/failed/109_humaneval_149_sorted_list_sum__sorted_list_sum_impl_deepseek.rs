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
/* helper modified by LLM (iteration 5): Add filter_even_length and insertion_sort helper functions */
fn filter_even_length(list: &Vec<Vec<char>>) -> Vec<Vec<char>>
    requires list@.len() > 0
    ensures result@.len() <= list@.len(),
            forall|i: int| 0 <= i < result@.len() ==> result@[i].len() % 2 == 0,
            result@.to_multiset().subset_of(list@.to_multiset())
{
    let mut result: Vec<Vec<char>> = Vec::new();
    let mut i: usize = 0;
    while i < list.len()
        invariant
            0 <= i <= list@.len(),
            result@.len() <= i,
            forall|j: int| 0 <= j < result@.len() ==> result@[j].len() % 2 == 0,
            result@.to_multiset().subset_of(list@.to_multiset())
    {
        if list[i].len() % 2 == 0 {
            result.push(list[i].clone());
        }
        i += 1;
    }
    result
}

fn insertion_sort(list: &mut Vec<Vec<char>>)
    requires list@.len() > 0
    ensures forall|x: int, y: int| 0 <= x < y < list@.len() ==> list@[x].len() <= list@[y].len(),
            list@.to_multiset() == old(list)@.to_multiset()
{
    let mut i: usize = 1;
    while i < list.len()
        invariant
            1 <= i <= list@.len(),
            forall|x: int, y: int| 0 <= x < y < i ==> list@[x].len() <= list@[y].len(),
            list@.to_multiset() == old(list)@.to_multiset()
    {
        let mut j = i;
        while j > 0 && list[j - 1].len() > list[j].len()
            invariant
                0 < j <= i,
                forall|x: int, y: int| 0 <= x < y < j ==> list@[x].len() <= list@[y].len(),
                forall|x: int, y: int| j <= x < y <= i ==> list@[x].len() <= list@[y].len(),
                list@.to_multiset() == old(list)@.to_multiset()
        {
            list.swap(j - 1, j);
            j -= 1;
        }
        i += 1;
    }
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
/* code modified by LLM (iteration 5): Implement main logic using helper functions */
{
    let mut filtered = filter_even_length(&list);
    insertion_sort(&mut filtered);
    filtered
}
// </vc-code>


}

fn main() {}