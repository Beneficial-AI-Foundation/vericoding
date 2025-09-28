// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn count_true_up_to(p: &Vec<bool>, k: int) -> int
    decreases k
{
    if k <= 0 {
        0
    } else {
        count_true_up_to(p, k - 1) + if p[(k - 1) as int] { 1 } else { 0 }
    }
}

proof fn lemma_count_true_bounds(p: &Vec<bool>, k: int)
    requires
        0 <= k <= p.len(),
    ensures
        0 <= count_true_up_to(p, k) <= k,
    decreases k
{
    if k > 0 {
        lemma_count_true_bounds(p, k - 1);
    }
}

proof fn lemma_count_true_monotonic(p: &Vec<bool>, i: int, j: int)
    requires
        0 <= i <= j <= p.len(),
    ensures
        count_true_up_to(p, i) <= count_true_up_to(p, j),
    decreases j - i
{
    if i < j {
        lemma_count_true_monotonic(p, i, j - 1);
    }
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
    let mut sorted = s.clone();
    let n = s.len();
    
    let mut i: usize = 0;
    while i < n
        invariant
            sorted.len() == n,
            s.len() == n,
            p.len() == n,
            0 <= i <= n,
            s@.to_multiset() == sorted@.to_multiset(),
            forall|k: int| 0 <= k < n && !p[k as int] ==> sorted[k] == s[k],
            forall|j: int, k: int| 0 <= j < i && j < k < n && p[j as int] && p[k as int] ==> sorted[j] as int <= sorted[k] as int,
    {
        if p[i as int] {
            let mut j: usize = i + 1;
            while j < n
                invariant
                    sorted.len() == n,
                    s.len() == n,
                    p.len() == n,
                    i < j <= n,
                    s@.to_multiset() == sorted@.to_multiset(),
                    forall|k: int| 0 <= k < n && !p[k as int] ==> sorted[k] == s[k],
                    forall|j_idx: int, k: int| 0 <= j_idx < i && j_idx < k < n && p[j_idx as int] && p[k as int] ==> sorted[j_idx] as int <= sorted[k] as int,
                    forall|k: int| i < k < j && p[k as int] ==> sorted[i] as int <= sorted[k] as int,
            {
                if p[j as int] && sorted[j] < sorted[i] {
                    let temp = sorted[i];
                    sorted.set(i, sorted[j]);
                    sorted.set(j, temp);
                }
                j = j + 1;
            }
        }
        i = i + 1;
    }
    
    sorted
}
// </vc-code>


}

fn main() {}