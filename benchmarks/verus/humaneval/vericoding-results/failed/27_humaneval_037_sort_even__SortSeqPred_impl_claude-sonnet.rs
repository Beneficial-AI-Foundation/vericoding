// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified swap helper with corrected multiset preservation */
fn swap_elements(s: &mut Vec<i8>, i: usize, j: usize)
    requires
        i < old(s).len(),
        j < old(s).len(),
    ensures
        s.len() == old(s).len(),
        s[i as int] == old(s)[j as int],
        s[j as int] == old(s)[i as int],
        forall|k: int| 0 <= k < s.len() && k != i && k != j ==> s[k] == old(s)[k],
        s@.to_multiset() == old(s)@.to_multiset(),
{
    let temp = s[i];
    s.set(i, s[j]);
    s.set(j, temp);
}
// </vc-helpers>

// <vc-spec>
fn sort_seq_pred(s: Vec<i8>, p: Vec<bool>) -> (sorted: Vec<i8>)
    requires s.len() == p.len(),
    ensures 
        sorted.len() == s.len(),
        forall|i: int, j: int| 0 <= i < j < sorted.len() && p[i as int] && p[j as int] ==> sorted[i] as int <= sorted[j] as int,
        s@.to_multiset() == sorted@.to_multiset(),
        forall|i: int| 0 <= i < s.len() && !p[i as int] ==> sorted[i] == s[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed bounds checking and invariant preservation */
    let mut sorted = s.clone();
    let n = sorted.len();
    
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            sorted.len() == n,
            n == s.len(),
            s.len() == p.len(),
            sorted@.to_multiset() == s@.to_multiset(),
            forall|k: int| 0 <= k < s.len() && !p[k as int] ==> sorted[k] == s[k],
            forall|x: int, y: int| 0 <= x < y < i && p[x as int] && p[y as int] ==> sorted[x] as int <= sorted[y] as int,
            forall|x: int, y: int| 0 <= x < i < y < n && p[x as int] && p[y as int] ==> sorted[x] as int <= sorted[y] as int,
        decreases n - i,
    {
        if p[i] {
            let mut min_idx = i;
            let mut j = i + 1;
            while j < n
                invariant
                    i < n,
                    i <= min_idx < n,
                    i + 1 <= j,
                    j <= n,
                    sorted.len() == n,
                    sorted@.to_multiset() == s@.to_multiset(),
                    forall|k: int| 0 <= k < s.len() && !p[k as int] ==> sorted[k] == s[k],
                    forall|k: int| i <= k < j && p[k as int] ==> sorted[min_idx as int] as int <= sorted[k] as int,
                decreases n - j,
            {
                if j < sorted.len() && p[j] && sorted[j] < sorted[min_idx] {
                    min_idx = j;
                }
                j += 1;
            }
            if min_idx != i {
                let temp = sorted[i];
                sorted.set(i, sorted[min_idx]);
                sorted.set(min_idx, temp);
            }
        }
        i += 1;
    }
    
    sorted
}
// </vc-code>


}

fn main() {}