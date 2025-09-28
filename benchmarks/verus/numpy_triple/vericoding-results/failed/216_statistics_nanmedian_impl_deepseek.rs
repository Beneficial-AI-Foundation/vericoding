// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix type conversions to use nat and proper ghost code */
proof fn lemma_finites_exist(a: Seq<f32>) -> (idx: int)
    requires
        has_finite_value(a),
    ensures
        0 <= idx < a.len(),
        a[idx] == a[idx],
{
    choose|i: int| 0 <= i < a.len() && (a[i] == a[i])
}

spec fn sorted_finites(seq: Seq<f32>) -> bool {
    forall|i: int, j: int| #![auto] 0 <= i <= j < seq.len() ==> (seq[i] == seq[i] && seq[j] == seq[j] && seq[i].spec_le(seq[j]))
}

proof fn lemma_median_properties(sorted: Seq<f32>) -> (median: f32)
    requires
        sorted.len() > 0,
        sorted_finites(sorted),
        forall|i: int| #![auto] 0 <= i < sorted.len() ==> (sorted[i] == sorted[i]),
    ensures
        median == median,
        exists|i: int| #![auto] 0 <= i < sorted.len() && sorted[i] == median
{
    let len: nat = sorted.len();
    if len % 2 == 1 {
        let mid: nat = len / 2;
        sorted[mid]
    } else {
        let mid1: nat = len / 2 - 1;
        let mid2: nat = len / 2;
        (sorted[mid1] as f32).spec_add(sorted[mid2]) / 2.0f32
    }
}
// </vc-helpers>

// <vc-spec>
spec fn all_nan(a: Seq<f32>) -> bool {
    forall|i: int| #![auto] 0 <= i < a.len() ==> (a[i] != a[i])
}

spec fn has_finite_value(a: Seq<f32>) -> bool {
    exists|i: int| #![auto] 0 <= i < a.len() && (a[i] == a[i])
}

fn nanmedian(a: Vec<f32>) -> (result: f32)
    ensures
        (all_nan(a@) ==> (result != result)) &&
        (has_finite_value(a@) ==> (result == result))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fix type conversion to use nat instead of int */
{
    if a.is_empty() {
        return f32::NAN;
    }
    
    let mut finites = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            forall|j: int| #![auto] 0 <= j < finites@.len() ==> finites@[j] == finites@[j],
        decreases a.len() - i
    {
        if a[i] == a[i] {
            finites.push(a[i]);
        }
        i += 1;
    }
    
    if finites.len() == 0 {
        return f32::NAN;
    }
    
    finites.sort_by(|x, y| x.partial_cmp(y).unwrap_or(std::cmp::Ordering::Equal));
    
    let len: usize = finites.len();
    if len % 2 == 1 {
        let mid: usize = len / 2;
        finites[mid]
    } else {
        let mid1: usize = len / 2 - 1;
        let mid2: usize = len / 2;
        (finites[mid1] + finites[mid2]) / 2.0f32
    }
}
// </vc-code>

}
fn main() {}