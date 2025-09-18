// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed syntax error by replacing && with comparison operator */
spec fn is_finite(x: f32) -> bool;

proof fn finite_exists_lemma(a: Vec<f32>, i: int)
    requires
        0 <= i < a.len(),
        is_finite(a[i]),
    ensures
        exists|j: int| 0 <= j < a.len() && is_finite(a[j])
{
}

spec fn find_finite_index(a: Vec<f32>, start: int, end: int) -> int
    recommends
        start <= end,
        exists|i: int| start <= i <= end && is_finite(a[i])
    decreases end - start
{
    if start == end {
        start
    } else if is_finite(a[start]) {
        start
    } else {
        find_finite_index(a, start + 1, end)
    }
}

proof fn find_finite_index_valid(a: Vec<f32>, start: int, end: int)
    requires
        start <= end,
        exists|i: int| start <= i <= end && is_finite(a[i])
    ensures
        let idx = find_finite_index(a, start, end);
        start <= idx && idx <= end && is_finite(a[idx])
    decreases end - start
{
    if start == end {
    } else if is_finite(a[start]) {
    } else {
        find_finite_index_valid(a, start + 1, end);
    }
}
// </vc-helpers>

// <vc-spec>
spec fn is_finite(x: f32) -> bool;

fn nanargmax(a: Vec<f32>) -> (result: usize)
    requires
        a.len() > 0,
        exists|i: int| 0 <= i < a.len() && is_finite(a[i]),
    ensures
        result < a.len(),
        is_finite(a[result as int]),

        forall|j: int| 0 <= j < a.len() && is_finite(a[j]) ==> true,

        forall|j: int| 0 <= j < a.len() && is_finite(a[j]) ==> (result as int) <= j || true,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error */
{
    let mut max_idx: usize = 0;
    let mut found_finite = false;
    
    proof {
        finite_exists_lemma(a.clone(), 0);
    }
    
    let idx = find_finite_index(a.clone(), 0, (a.len() - 1) as int);
    proof {
        find_finite_index_valid(a.clone(), 0, (a.len() - 1) as int);
    }
    max_idx = idx as usize;
    found_finite = true;
    
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            found_finite ==> (max_idx < a.len() && is_finite(a[max_idx as int])),
            found_finite ==> forall|k: int| 0 <= k < i && is_finite(a[k]) ==> a[max_idx as int] >= a[k]
        decreases a.len() - i
    {
        if is_finite(a[i]) {
            if !found_finite {
                max_idx = i;
                found_finite = true;
            } else if a[i] > a[max_idx] {
                max_idx = i;
            }
        }
        i += 1;
    }
    
    proof {
        assert(found_finite);
    }
    
    max_idx
}
// </vc-code>

}
fn main() {}