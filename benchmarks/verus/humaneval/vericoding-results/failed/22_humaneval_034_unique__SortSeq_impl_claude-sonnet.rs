// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed problematic proof block from swap function */
fn min_index(v: &Vec<i8>, start: usize) -> (min_idx: usize)
    requires
        start < v@.len(),
    ensures
        start <= min_idx < v@.len(),
        forall|i: int| start <= i < v@.len() ==> v@[min_idx as int] <= v@[i],
{
    let mut min_idx = start;
    let mut i = start;
    while i < v.len()
        invariant
            start <= min_idx < v@.len(),
            start <= i <= v@.len(),
            forall|j: int| start <= j < i ==> v@[min_idx as int] <= v@[j],
        decreases v@.len() - i,
    {
        if v[i] < v[min_idx] {
            min_idx = i;
        }
        i += 1;
    }
    min_idx
}

fn swap(v: &mut Vec<i8>, i: usize, j: usize)
    requires
        i < old(v)@.len(),
        j < old(v)@.len(),
    ensures
        v@.len() == old(v)@.len(),
        v@[i as int] == old(v)@[j as int],
        v@[j as int] == old(v)@[i as int],
        forall|k: int| 0 <= k < v@.len() && k != i && k != j ==> v@[k] == old(v)@[k],
        v@.to_multiset() == old(v)@.to_multiset(),
{
    let temp = v[i];
    v.set(i, v[j]);
    v.set(j, temp);
}
// </vc-helpers>

// <vc-spec>
fn sort_seq(s: Vec<i8>) -> (sorted: Vec<i8>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < sorted@.len() ==> sorted@[i] <= sorted@[j],
        sorted@.len() == s@.len(),
        s@.to_multiset() == sorted@.to_multiset()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed arithmetic overflow and loop invariant issues */
    let mut result = s;
    let mut i = 0;
    while i < result.len()
        invariant
            result@.len() == s@.len(),
            result@.to_multiset() == s@.to_multiset(),
            0 <= i <= result@.len(),
            forall|a: int, b: int| 0 <= a < b < i ==> result@[a] <= result@[b],
            forall|a: int, b: int| 0 <= a < i && i <= b < result@.len() ==> result@[a] <= result@[b],
        decreases result@.len() - i,
    {
        if i < result.len() {
            let min_idx = min_index(&result, i);
            if min_idx != i {
                swap(&mut result, i, min_idx);
            }
        }
        i += 1;
    }
    result
}
// </vc-code>


}

fn main() {}