#![verifier::loop_isolation(false)]
use vstd::math::*;
use vstd::prelude::*;

verus! {

spec fn max_rcur(seq: Seq<i32>) -> (result:int)
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        max(seq.last() as int, max_rcur(seq.drop_last()))
    }
}
// pure-end
// pure-end

spec fn min_rcur(seq: Seq<i32>) -> (result:int)
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        min(seq.last() as int, min_rcur(seq.drop_last()))
    }
}
// pure-end

// <vc-helpers>
proof fn max_rcur_bounds(seq: Seq<i32>)
    requires seq.len() > 0,
    ensures 
        exists|i: int| 0 <= i < seq.len() && max_rcur(seq) == seq[i],
        forall|i: int| 0 <= i < seq.len() ==> seq[i] <= max_rcur(seq),
    decreases seq.len(),
{
    /* code modified by LLM (iteration 4): fixed assertions for drop_last properties */
    if seq.len() <= 1 {
        assert(max_rcur(seq) == seq.first() as int);
        assert(seq.first() == seq[0]);
        assert(exists|i: int| 0 <= i < seq.len() && max_rcur(seq) == seq[i]);
        assert(forall|i: int| 0 <= i < seq.len() ==> seq[i] <= max_rcur(seq));
    } else {
        max_rcur_bounds(seq.drop_last());
        assert(seq.drop_last().len() > 0);
        
        let last_val = seq.last() as int;
        let rest_max = max_rcur(seq.drop_last());
        let full_max = max_rcur(seq);
        
        assert(full_max == max(last_val, rest_max));
        
        /* code modified by LLM (iteration 4): established drop_last correspondence */
        assert(forall|i: int| 0 <= i < seq.drop_last().len() ==> seq[i] == seq.drop_last()[i]);
        assert(forall|i: int| 0 <= i < seq.drop_last().len() ==> seq.drop_last()[i] <= rest_max);
        assert(forall|i: int| 0 <= i < seq.drop_last().len() ==> seq[i] <= rest_max);
        
        if last_val >= rest_max {
            assert(full_max == last_val);
            assert(seq[seq.len() - 1] == seq.last());
            assert(exists|i: int| 0 <= i < seq.len() && max_rcur(seq) == seq[i]);
        } else {
            assert(full_max == rest_max);
            assert(exists|i: int| 0 <= i < seq.drop_last().len() && rest_max == seq.drop_last()[i]);
            assert(exists|i: int| 0 <= i < seq.len() && max_rcur(seq) == seq[i]);
        }
        
        assert(forall|i: int| 0 <= i < seq.drop_last().len() ==> seq[i] <= full_max);
        assert(seq[seq.len() - 1] <= full_max);
        assert(forall|i: int| 0 <= i < seq.len() ==> seq[i] <= max_rcur(seq));
    }
}

proof fn min_rcur_bounds(seq: Seq<i32>)
    requires seq.len() > 0,
    ensures 
        exists|i: int| 0 <= i < seq.len() && min_rcur(seq) == seq[i],
        forall|i: int| 0 <= i < seq.len() ==> min_rcur(seq) <= seq[i],
    decreases seq.len(),
{
    /* code modified by LLM (iteration 4): fixed assertions for drop_last properties */
    if seq.len() <= 1 {
        assert(min_rcur(seq) == seq.first() as int);
        assert(seq.first() == seq[0]);
        assert(exists|i: int| 0 <= i < seq.len() && min_rcur(seq) == seq[i]);
        assert(forall|i: int| 0 <= i < seq.len() ==> min_rcur(seq) <= seq[i]);
    } else {
        min_rcur_bounds(seq.drop_last());
        assert(seq.drop_last().len() > 0);
        
        let last_val = seq.last() as int;
        let rest_min = min_rcur(seq.drop_last());
        let full_min = min_rcur(seq);
        
        assert(full_min == min(last_val, rest_min));
        
        /* code modified by LLM (iteration 4): established drop_last correspondence */
        assert(forall|i: int| 0 <= i < seq.drop_last().len() ==> seq[i] == seq.drop_last()[i]);
        assert(forall|i: int| 0 <= i < seq.drop_last().len() ==> rest_min <= seq.drop_last()[i]);
        assert(forall|i: int| 0 <= i < seq.drop_last().len() ==> rest_min <= seq[i]);
        
        if last_val <= rest_min {
            assert(full_min == last_val);
            assert(seq[seq.len() - 1] == seq.last());
            assert(exists|i: int| 0 <= i < seq.len() && min_rcur(seq) == seq[i]);
        } else {
            assert(full_min == rest_min);
            assert(exists|i: int| 0 <= i < seq.drop_last().len() && rest_min == seq.drop_last()[i]);
            assert(exists|i: int| 0 <= i < seq.len() && min_rcur(seq) == seq[i]);
        }
        
        assert(forall|i: int| 0 <= i < seq.drop_last().len() ==> full_min <= seq[i]);
        assert(full_min <= seq[seq.len() - 1]);
        assert(forall|i: int| 0 <= i < seq.len() ==> min_rcur(seq) <= seq[i]);
    }
}

fn find_max(arr: &Vec<i32>) -> (result: i32)
    requires arr.len() > 0,
    ensures 
        result == max_rcur(arr@),
        exists|i: int| 0 <= i < arr.len() && result == arr[i],
{
    let mut max_val = arr[0];
    let mut i = 1;
    
    while i < arr.len()
        invariant
            0 < i <= arr.len(),
            exists|j: int| 0 <= j < i && max_val == arr[j],
            forall|j: int| 0 <= j < i ==> arr[j] <= max_val,
            max_val == max_rcur(arr@.subrange(0, i as int)),
        decreases arr.len() - i,
    {
        /* code modified by LLM (iteration 4): corrected subseq construction and assertions */
        proof {
            let prev_subseq = arr@.subrange(0, i as int);
            let new_subseq = arr@.subrange(0, (i + 1) as int);
            
            assert(new_subseq.len() == prev_subseq.len() + 1);
            assert(new_subseq.drop_last() == prev_subseq);
            assert(new_subseq.last() == arr[i as int]);
            assert(max_rcur(new_subseq) == max(arr[i as int] as int, max_rcur(prev_subseq)));
        }
        
        if arr[i] > max_val {
            max_val = arr[i];
        }
        i += 1;
    }
    
    proof {
        assert(arr@.subrange(0, arr.len() as int) == arr@);
    }
    
    max_val
}

fn find_min(arr: &Vec<i32>) -> (result: i32)
    requires arr.len() > 0,
    ensures 
        result == min_rcur(arr@),
        exists|i: int| 0 <= i < arr.len() && result == arr[i],
{
    let mut min_val = arr[0];
    let mut i = 1;
    
    while i < arr.len()
        invariant
            0 < i <= arr.len(),
            exists|j: int| 0 <= j < i && min_val == arr[j],
            forall|j: int| 0 <= j < i ==> min_val <= arr[j],
            min_val == min_rcur(arr@.subrange(0, i as int)),
        decreases arr.len() - i,
    {
        /* code modified by LLM (iteration 4): corrected subseq construction and assertions */
        proof {
            let prev_subseq = arr@.subrange(0, i as int);
            let new_subseq = arr@.subrange(0, (i + 1) as int);
            
            assert(new_subseq.len() == prev_subseq.len() + 1);
            assert(new_subseq.drop_last() == prev_subseq);
            assert(new_subseq.last() == arr[i as int]);
            assert(min_rcur(new_subseq) == min(arr[i as int] as int, min_rcur(prev_subseq)));
        }
        
        if arr[i] < min_val {
            min_val = arr[i];
        }
        i += 1;
    }
    
    proof {
        assert(arr@.subrange(0, arr.len() as int) == arr@);
    }
    
    min_val
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

// <vc-spec>
fn sum_min_max(arr: &Vec<i32>) -> (sum: i32)
    // pre-conditions-start
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        sum == max_rcur(arr@) + min_rcur(arr@),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let max_val = find_max(arr);
    let min_val = find_min(arr);
    
    proof {
        max_rcur_bounds(arr@);
        min_rcur_bounds(arr@);
    }
    
    max_val + min_val
}
// </vc-code>

} // verus!

fn main() {}