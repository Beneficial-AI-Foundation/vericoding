// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added decreases clause to count_non_pred and fixed partition_preserves_non_pred */
// Helper function to partition sequence based on predicate
spec fn partition_seq<T>(s: Seq<T>, p: Seq<bool>, f_idx: int, t_idx: int) -> Seq<T>
    decreases s.len()
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        let head_val = s[0];
        let head_pred = p[0];
        let tail_s = s.subrange(1, s.len() as int);
        let tail_p = p.subrange(1, p.len() as int);
        
        if head_pred {
            partition_seq(tail_s, tail_p, f_idx, t_idx + 1).insert(t_idx, head_val)
        } else {
            partition_seq(tail_s, tail_p, f_idx + 1, t_idx).insert(f_idx, head_val)
        }
    }
}

// Helper lemma proving partition preserves multiset
proof fn partition_preserves_multiset<T>(s: Seq<T>, p: Seq<bool>, f_idx: int, t_idx: int)
    ensures
        s.to_multiset() == partition_seq(s, p, f_idx, t_idx).to_multiset(),
    decreases s.len(),
{
    if s.len() > 0 {
        let head_val = s[0];
        let head_pred = p[0];
        let tail_s = s.subrange(1, s.len() as int);
        let tail_p = p.subrange(1, p.len() as int);
        
        partition_preserves_multiset(tail_s, tail_p, if head_pred { f_idx } else { f_idx + 1 }, if head_pred { t_idx + 1 } else { t_idx });
    }
}

spec fn count_non_pred(p: Seq<bool>, up_to: int) -> int
    decreases up_to
{
    if up_to <= 0 {
        0
    } else {
        count_non_pred(p, up_to - 1) + (if !p[up_to - 1] { 1 } else { 0 })
    }
}

// Helper lemma proving non-predicate elements stay in place
proof fn partition_preserves_non_pred<T>(s: Seq<T>, p: Seq<bool>, f_idx: int, t_idx: int)
    ensures
        forall|i: int| 0 <= i < s.len() && !p[i] ==> partition_seq(s, p, f_idx, t_idx)[f_idx + count_non_pred(p, i)] == s[i],
    decreases s.len(),
{
    if s.len() > 0 {
        let head_val = s[0];
        let head_pred = p[0];
        let tail_s = s.subrange(1, s.len() as int);
        let tail_p = p.subrange(1, p.len() as int);
        
        if head_pred {
            partition_preserves_non_pred(tail_s, tail_p, f_idx, t_idx + 1);
        } else {
            partition_preserves_non_pred(tail_s, tail_p, f_idx + 1, t_idx);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn sort_seq_pred(s: Vec<i8>, p: Vec<bool>) -> (sorted: Vec<i8>)
  requires s.len() == p.len(),
  ensures 
    sorted.len() == s.len(),
    forall|i: int, j: int| 0 <= i < j < sorted.len() && p[i] && p[j] ==> sorted[i] as int <= sorted[j] as int,
    s@.to_multiset() == sorted@.to_multiset(),
    forall|i: int| 0 <= i < s.len() && !p[i] ==> sorted[i] == s[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Implementation using partition and sort */
    let mut sorted = s.clone();
    let mut pred_indices = Vec::new();
    let mut pred_values = Vec::new();
    
    let mut i = 0;
    while i < sorted.len()
        invariant
            i <= sorted.len(),
            sorted@.to_multiset() == s@.to_multiset(),
            forall|j: int| 0 <= j < i && !p[j] ==> sorted[j] == s[j],
    {
        if p[i] {
            pred_indices.push(i);
            pred_values.push(sorted[i]);
        }
        i += 1;
    }
    
    pred_values.sort();
    
    let mut j = 0;
    while j < pred_indices.len()
        invariant
            j <= pred_indices.len(),
            sorted@.to_multiset() == s@.to_multiset(),
            forall|k: int| 0 <= k < sorted.len() && !p[k] ==> sorted[k] == s[k],
            forall|k1: int, k2: int| 0 <= k1 < k2 < j && p[pred_indices[k1] as int] && p[pred_indices[k2] as int] ==> sorted[pred_indices[k1] as usize] as int <= sorted[pred_indices[k2] as usize] as int,
    {
        let idx = pred_indices[j];
        sorted.set(idx, pred_values[j]);
        j += 1;
    }
    
    sorted
}
// </vc-code>


}

fn main() {}