// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): get_min_index computes index of minimal element from start */
fn get_min_index(a: &Vec<i32>, start: usize) -> (result: usize)
    requires
        start < a.len(),
    ensures
        start <= result && result < a.len(),
        forall|t: int| start as int <= t && t < a.len() as int ==> a@[result as int] <= a@[t as int],
{
    let mut m: usize = start;
    let mut j: usize = start + 1;
    while j < a.len()
        invariant
            start <= m && m < a.len(),
            start <= j && j <= a.len(),
            forall|t: int| start as int <= t && t < j as int ==> a@[m as int] <= a@[t],
        decreases a.len() - j
    {
        if a[j] < a[m] {
            m = j;
        }
        j = j + 1;
    }
    m
}

/* helper modified by LLM (iteration 5): vec_swap_preserve swaps two elements and preserves multiset */
fn vec_swap_preserve(a: &mut Vec<i32>, i: usize, j: usize)
    requires
        i < old(a).len(), j < old(a).len(),
    ensures
        a.len() == old(a).len(),
        a@ =~= old(a)@,
{
    let tmp = a[i];
    a[i] = a[j];
    a[j] = tmp;
    proof {
        assert(forall|k: int| 0 <= k && k < a.len() as int ==>
            if k == i as int { a@[k] == old(a)@[j as int] } else if k == j as int { a@[k] == old(a)@[i as int] } else { a@[k] == old(a)@[k] });
        assert(a@ =~= old(a)@);
    }
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i <= j < result.len() ==> result[i] <= result[j],
        result@ =~= a@,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): selection sort implementation using get_min_index and vec_swap_preserve */
    let mut result = a.clone();
    let n: usize = result.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == n,
            result@ =~= a@,
            forall|k: int, l: int| 0 <= k <= l < i as int ==> result@[k] <= result@[l],
        decreases n - i
    {
        let m = get_min_index(&result, i);
        vec_swap_preserve(&mut result, i, m);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}