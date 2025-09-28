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
/* helper modified by LLM (iteration 5): fixed multiset preservation in selection sort */
fn selection_sort(v: &mut Vec<Vec<char>>)
    requires
        old(v)@.len() >= 0,
    ensures
        v@.len() == old(v)@.len(),
        forall|i: int, j: int| 0 <= i < j < v@.len() ==> v@[i].len() <= v@[j].len(),
        v@.to_multiset() == old(v)@.to_multiset(),
{
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            v@.len() == old(v)@.len(),
            forall|x: int, y: int| 0 <= x < y < i ==> v@[x].len() <= v@[y].len(),
            forall|x: int, y: int| 0 <= x < i && i <= y < v@.len() ==> v@[x].len() <= v@[y].len(),
            v@.to_multiset() =~= old(v)@.to_multiset(),
        decreases v.len() - i
    {
        let mut min_idx = i;
        let mut j = i + 1;
        while j < v.len()
            invariant
                i <= min_idx < v.len(),
                i + 1 <= j <= v@.len(),
                forall|k: int| i <= k < j ==> v@[min_idx as int].len() <= v@[k].len(),
            decreases v.len() - j
        {
            if v[j].len() < v[min_idx].len() {
                min_idx = j;
            }
            j += 1;
        }
        
        if min_idx != i {
            let old_v = v@;
            let temp = v[i].clone();
            v.set(i, v[min_idx].clone());
            v.set(min_idx, temp);
            assert(v@.to_multiset() =~= old_v.to_multiset());
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
{
    /* code modified by LLM (iteration 5): fixed subset invariant and postcondition */
    let mut filtered: Vec<Vec<char>> = Vec::new();
    let mut i = 0;
    while i < list.len()
        invariant
            0 <= i <= list.len(),
            filtered@.len() <= i,
            forall|j: int| 0 <= j < filtered@.len() ==> filtered@[j].len() % 2 == 0,
            forall|j: int| 0 <= j < filtered@.len() ==> list@.contains(filtered@[j]),
        decreases list.len() - i
    {
        if list[i].len() % 2 == 0 {
            filtered.push(list[i].clone());
            assert(list@.contains(list@[i as int]));
        }
        i += 1;
    }
    
    selection_sort(&mut filtered);
    
    proof {
        assert(forall|j: int| 0 <= j < filtered@.len() ==> filtered@[j].len() % 2 == 0);
        assert(filtered@.to_multiset().subset_of(list@.to_multiset()));
    }
    
    filtered
}
// </vc-code>


}

fn main() {}