use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn max(a: i32, b: i32) -> i32 {
    if a >= b { a } else { b }
}

spec fn max_in_range(seq: Seq<i32>, lo: int, hi: int) -> i32 
    recommends 0 <= lo < hi <= seq.len()
    decreases hi - lo
{
    if hi - lo == 1 {
        seq[lo]
    } else {
        let mid = lo + (hi - lo)/2;
        max(max_in_range(seq, lo, mid), max_in_range(seq, mid, hi))
    }
}

proof fn lemma_max_exists(seq: Seq<i32>, lo: int, hi: int) 
    requires 
        0 <= lo <= hi <= seq.len(),
        hi - lo > 0,
    ensures 
        exists|i: int| lo <= i < hi && seq[i] == max_in_range(seq, lo, hi)
    decreases hi - lo
{
    if hi - lo == 1 {
        // Base case: only one element
    } else {
        let mid = lo + (hi - lo)/2;
        lemma_max_exists(seq, lo, mid);
        lemma_max_exists(seq, mid, hi);
    }
}

proof fn lemma_max_in_range_properties(seq: Seq<i32>, lo: int, hi: int, i: int)
    requires 
        0 <= lo <= hi <= seq.len(),
        lo <= i < hi,
    ensures 
        seq[i] <= max_in_range(seq, lo, hi)
    decreases hi - lo
{
    if hi - lo == 1 {
        // Base case: only one element
    } else {
        let mid = lo + (hi - lo)/2;
        if i < mid {
            lemma_max_in_range_properties(seq, lo, mid, i);
        } else {
            lemma_max_in_range_properties(seq, mid, hi, i);
        }
    }
}

proof fn lemma_max_val_correct(a_seq: Seq<i32>, idx: int, max_val: i32)
    requires
        0 <= idx <= a_seq.len(),
        forall|j: int| 0 <= j < idx ==> a_seq[j] <= max_val,
        exists|j: int| 0 <= j < idx && a_seq[j] == max_val,
    ensures
        max_val >= max_in_range(a_seq, 0, a_seq.len() as int)
{
    lemma_max_exists(a_seq, 0, a_seq.len() as int);
    assert forall|i: int| 0 <= i < a_seq.len() implies a_seq[i] <= max_in_range(a_seq, 0, a_seq.len() as int) by {
        lemma_max_in_range_properties(a_seq, 0, a_seq.len() as int, i);
    };
}
// </vc-helpers>

// <vc-spec>
fn max_element(a: &Vec<i32>) -> (max: i32)
    // pre-conditions-start
    requires
        a.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int| 0 <= i < a.len() ==> a[i] <= max,
        exists|i: int| 0 <= i < a.len() && a[i] == max,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut max_val = a[0];
    let mut idx: usize = 0;
    let a_seq = a.view();
    
    while idx < a.len()
        invariant 
            0 <= idx <= a.len(),
            forall|j: int| 0 <= j < idx ==> a_seq@[j] <= max_val,
            exists|j: int| 0 <= j < idx && a_seq@[j] == max_val,
        decreases a.len() - idx
    {
        if a[idx] > max_val {
            max_val = a[idx];
        }
        idx = idx + 1;
    }
    
    proof {
        lemma_max_val_correct(a_seq, idx as int, max_val);
    }
    
    max_val
}
// </vc-code>

fn main() {}
}