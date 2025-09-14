// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_frequency_rcr(seq: Seq<i32>, key: i32) -> (result: int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_frequency_rcr(seq.drop_last(), key) + if (seq.last() == key) {
            1 as int
        } else {
            0 as int
        }
    }
}
// </vc-preamble>

// <vc-helpers>
spec fn contains(seq: Seq<i32>, key: i32) -> bool {
    seq.contains(key)
}

spec fn count_frequency_iter(seq: Seq<i32>, key: i32, idx: int) -> int
    decreases seq.len() - idx,
{
    if idx >= seq.len() {
        0
    } else {
        (if seq[idx] == key { 1int } else { 0int }) + count_frequency_iter(seq, key, idx + 1)
    }
}

/* helper modified by LLM (iteration 5): fixed proof logic to establish proper equivalence */
proof fn count_frequency_equivalence_helper(seq: Seq<i32>, key: i32, idx: int)
    requires 0 <= idx <= seq.len(),
    ensures count_frequency_rcr(seq.subrange(idx, seq.len() as int), key) == count_frequency_iter(seq, key, idx),
    decreases seq.len() - idx,
{
    if idx < seq.len() {
        let subseq = seq.subrange(idx, seq.len() as int);
        let tail_subseq = seq.subrange(idx + 1, seq.len() as int);
        
        count_frequency_equivalence_helper(seq, key, idx + 1);
        
        assert(subseq.drop_last() == tail_subseq);
        assert(subseq.last() == seq[idx]);
    }
}

proof fn count_frequency_equivalence(seq: Seq<i32>, key: i32)
    ensures count_frequency_rcr(seq, key) == count_frequency_iter(seq, key, 0),
{
    count_frequency_equivalence_helper(seq, key, 0);
}
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>)

    ensures
        unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed invariants and overflow issues */
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
        decreases arr.len() - i,
    {
        let current = arr[i];
        let mut count: u32 = 0;
        let mut j = 0;
        
        while j < arr.len()
            invariant
                0 <= j <= arr.len(),
                count as int == count_frequency_iter(arr@, current, 0) - count_frequency_iter(arr@, current, j as int),
                count < arr.len(),
            decreases arr.len() - j,
        {
            if arr[j] == current {
                count = count + 1;
            }
            j = j + 1;
        }
        
        proof {
            count_frequency_equivalence(arr@, current);
        }
        
        if count == 1 {
            result.push(current);
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}